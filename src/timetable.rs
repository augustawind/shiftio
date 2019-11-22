use std::cmp::Ordering;
use std::fmt::Debug;
use std::ops::{Add, Sub};

use chrono::{DateTime, Datelike, NaiveTime, TimeZone, Utc, Weekday};
use indexmap::IndexMap;
use time::Duration;

const DUMMY_YEAR: i32 = 1970;
const DUMMY_WEEK: u32 = 1;

/// Represents a naive time on a day of the week.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WeekTime {
    weekday: Weekday,
    time: NaiveTime,
}

impl PartialOrd for WeekTime {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for WeekTime {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.day_of_week().cmp(&other.day_of_week()) {
            Ordering::Equal => self.time.cmp(&other.time),
            ord => ord,
        }
    }
}

impl WeekTime {
    /// Create a new `WeekTime` from a weekday, an hour, and a minute.
    pub fn new(weekday: Weekday, hour: u32, min: u32) -> Option<Self> {
        let time = NaiveTime::from_hms_opt(hour, min, 0)?;
        Some(Self::from_time(weekday, time))
    }

    /// Create a new `WeekTime` from a weekday and a naive time.
    pub fn from_time(weekday: Weekday, time: NaiveTime) -> Self {
        WeekTime { weekday, time }
    }

    fn dt(&self) -> DateTime<Utc> {
        // WARNING: using `unwrap()` here because it doesn't look like it's possible for this
        // to fail when using the `Utc` timezone. Handle this properly if you ever change the TZ.
        Utc.isoywd(DUMMY_YEAR, DUMMY_WEEK, self.weekday)
            .and_time(self.time)
            .unwrap()
    }

    /// Returns the weekday as a number from 0-6.
    pub fn day_of_week(&self) -> u32 {
        self.weekday.num_days_from_monday()
    }

    /// Returns the number of days from `self.weekday` to the end of the week.
    /// Sunday is considered the end of the week. The result will be a uint in the range `[0..6]`,
    /// e.g. if `self.weekday` is Sunday this function will return `0`.
    pub fn days_left_in_week(&self) -> u32 {
        6 - self.day_of_week()
    }

    /// Return the number of
    pub fn seconds_until_tomorrow(&self) -> u32 {
        let time = self.time - NaiveTime::from_hms(0, 0, 0);
        (Duration::hours(24) - time).num_seconds() as u32
    }
}

impl Add<Duration> for WeekTime {
    type Output = Self;

    fn add(self, duration: Duration) -> Self {
        let datetime = self.dt() + duration;
        WeekTime {
            weekday: datetime.weekday(),
            time: datetime.time(),
        }
    }
}

impl Sub<Duration> for WeekTime {
    type Output = Self;

    fn sub(self, duration: Duration) -> Self {
        let datetime = self.dt() - duration;
        WeekTime {
            weekday: datetime.weekday(),
            time: datetime.time(),
        }
    }
}

impl Sub<WeekTime> for WeekTime {
    type Output = Duration;

    fn sub(self, weektime: WeekTime) -> Duration {
        self.dt() - weektime.dt()
    }
}

/// Represents a period between two points in time within a week (a 7-day period).
///
/// A `TimeRange` is meaningful only within the context of an arbitrary week: its start and end
/// times are represented as [`WeekTime`] objects, which have no concept of time outside of that.
/// Therefore, implementors are expected to enforce certain invariants to keep things sane and
/// meaningful:
///
/// - The start and end times must be in the same [week](src.lib.html#Weeks).
/// - The end time must be _after_ the start time.
///
/// This means that the later the start time is in the week, the smaller the range of possible values
/// for the end time. For example, if the start time is on Saturday at 15:00, the end time must be
/// between Saturday @ 15:00 and Monday @ 00:00.
///
/// The [`init_pair`] and [`init_duration`] trait methods are provided to help implementors enforce
/// these properties in their constructor functions.
///
/// # Example
///
/// ```rust
/// use shiftio::{Duration, TimeRange, Weekday::*, WeekTime};
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct MyTimeRange {
///     start: WeekTime,
///     end: WeekTime,
/// }
///
/// impl TimeRange for MyTimeRange {
///     fn start(&self) -> WeekTime {
///         self.start
///     }
///     fn end(&self) -> WeekTime {
///         self.end
///     }
/// }
///
/// impl MyTimeRange {
///     // A constructor function that takes a start and end time, and
///     // validates them using `TimeRange::init_pair`.
///     fn new(start: WeekTime, end: WeekTime) -> Option<Self> {
///         let (start, end) = Self::init_pair(start, end)?;
///         Some(MyTimeRange { start, end })
///     }
///
///     // A constructor function that takes a start time and a duration, and
///     // validates them using `TimeRange::init_duration`. This also returns
///     // the end time.
///     fn from_duration(start: WeekTime, duration: Duration) -> Option<Self> {
///         let (start, end) = Self::init_duration(start, duration)?;
///         Some(MyTimeRange { start, end })
///     }
/// }
///
/// // Validation fails: end < start.
/// let result = MyTimeRange::new(
///     WeekTime::new(Wed, 0, 0).unwrap(),
///     WeekTime::new(Tue, 0, 0).unwrap(),
/// );
/// assert!(result.is_none());
///
/// // Validation fails: end time (start + duration) would be in following week.
/// let result = MyTimeRange::from_duration(
///     WeekTime::new(Sun, 20, 0).unwrap(),
///     Duration::hours(8),
/// );
/// assert!(result.is_none());
/// ```
///
pub trait TimeRange: Debug + Clone + PartialEq + Eq {
    fn start(&self) -> WeekTime;
    fn end(&self) -> WeekTime;

    /// Initialize a (start_time, end_time) pair.
    ///
    /// Returns the pair, or [`None`] if `end` is before or equal to `start`.
    ///
    /// Implementors should call this in their constructor functions that accept start and end
    /// times as parameters.
    fn init_pair(start: WeekTime, end: WeekTime) -> Option<(WeekTime, WeekTime)> {
        if end <= start {
            return None;
        }
        Some((start, end))
    }

    /// Initialize a (start time, end time) pair from a start time and a duration.
    ///
    /// Calculates the end time by adding the duration to the start time. Returns [`None`] if
    /// `duration` is zero or negative, or if the end time would be in a different week (weeks start
    /// on Monday and end on Sunday). For example, if `start` is on a Friday and `duration` is 3
    /// days, the end time would be on Monday of next week, so [`None`] would be returned.
    ///
    /// Returns a (start_time, end_time) pair if `duration` is valid.
    ///
    /// Implementors should call this in their constructor functions that accept a start time and
    /// a duration as parameters.
    fn init_duration(start: WeekTime, duration: Duration) -> Option<(WeekTime, WeekTime)> {
        // TODO: insert these debug stmts into actual errors in a Result.

        // Assert duration is greater than zero.
        if duration <= Duration::zero() {
            eprintln!("Duration is <= zero.");
            return None;
        }

        // Assert duration is not longer than remaining time in week.
        let days_left = start.days_left_in_week() as i64;
        let seconds_left = start.seconds_until_tomorrow() as i64;

        if duration >= Duration::days(days_left) + Duration::seconds(seconds_left) {
            return None;
        }

        let end = start + duration;
        Some((start, end))
    }

    /// Returns `true` if this `TimeRange` and the given `range` overlap.
    fn intersects(&self, other: &Self) -> bool {
        other.start() < self.end() && other.end() > self.start()
    }
}

pub trait Timetable<T: TimeRange> {
    /// Should return a reference to the ranges map in this `Timetable`.
    fn ranges(&self) -> &IndexMap<WeekTime, T>;

    /// Should return a mutable reference to the ranges map in this `Timetable`.
    ///
    /// Avoid using this method directly. Instead, use [`add_range`], [`add_ranges`], and
    /// [`rm_range`] to safely modify the `Timetable`.
    fn ranges_mut(&mut self) -> &mut IndexMap<WeekTime, T>;

    /// Adds a [`TimeBlock`] to the Agenda.
    ///
    /// If the time block overlaps with any blocks in the Agenda, an Err is returned with a vector
    /// of all the time blocks it overlapped in ascending order.
    fn add_range(&mut self, range: T) -> Result<(), Vec<T>> {
        let overlapping = self.find_overlapping(&range);
        if !overlapping.is_empty() {
            return Err(overlapping);
        }

        let rs = self.ranges_mut();
        rs.insert(range.start(), range);
        rs.sort_keys();

        Ok(())
    }

    /// Adds multiple [`T`]s to the Agenda.
    ///
    /// If any time blocks in `iter` overlap with any blocks in the Agenda, an Err is returned
    /// with a tuple of `(index, block, overlapping)`, where `block` is the first block in `iter`
    /// that overlapped, `index` is its index in `iter`, and `overlapping` is a vector of all
    /// the blocks it overlapped in the Agenda in ascending order. Note that this includes
    /// duplicates as well.
    ///
    /// This is more efficient than calling [`add_range`] individually for each time block.
    fn add_ranges<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), (usize, T, Vec<T>)> {
        let mut ranges = Vec::new();

        for (i, range) in iter.into_iter().enumerate() {
            let overlapping = self.find_overlapping(&range);
            if !overlapping.is_empty() {
                return Err((i, range, overlapping));
            }
            ranges.push(range);
        }

        let rs = self.ranges_mut();
        for range in ranges {
            rs.insert(range.start(), range);
        }
        rs.sort_keys();

        Ok(())
    }

    /// Removes the range with the given `start_time`.
    ///
    /// Returns the removed range, or [`None`] if it can't be found.
    fn rm_range(&mut self, start_time: WeekTime) -> Option<T> {
        self.ranges_mut().shift_remove(&start_time)
    }

    /// Returns all ranges in `self.ranges()` that are overlapped by `range`.
    ///
    /// This is used by [`add_range`] and [`add_ranges`] to validate incoming ranges.
    fn find_overlapping(&self, range: &T) -> Vec<T> {
        self.ranges()
            .values()
            .filter_map(|r| {
                if range.intersects(r) {
                    Some(r.clone())
                } else {
                    None
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn wt() -> WeekTime {
        wt_with(Weekday::Thu, 11)
    }

    fn wt_with(weekday: Weekday, hour: u32) -> WeekTime {
        WeekTime::new(weekday, hour, 0).unwrap()
    }

    mod test_time_range {
        use super::*;

        use chrono::Timelike;

        // TimeSpan implements TimeRange for testing.
        #[derive(Debug, Clone, PartialEq, Eq)]
        struct TimeSpan(WeekTime, WeekTime);
        impl TimeRange for TimeSpan {
            fn start(&self) -> WeekTime {
                self.0
            }
            fn end(&self) -> WeekTime {
                self.1
            }
        }
        impl TimeSpan {
            fn from_duration(start: WeekTime, duration: Duration) -> Option<Self> {
                let (start, end) = Self::init_duration(start, duration)?;
                Some(Self(start, end))
            }
        }

        #[test]
        fn test_init_pair() {
            let start = wt();
            let end = start;
            assert!(
                TimeSpan::init_pair(start, end).is_none(),
                "it should fail if start == end"
            );

            let start = wt();
            let end = start - Duration::hours(1);
            assert!(
                TimeSpan::init_pair(start, end).is_none(),
                "it should fail if start > end"
            );
        }

        #[test]
        fn test_init_duration() {
            // happy path
            let start = wt();
            let duration = Duration::hours(8);
            let range = TimeSpan::from_duration(start, duration).unwrap();
            assert_eq!(range.end() - range.start(), duration);

            // happy path (maximum possible duration)
            let start = wt_with(Weekday::Sun, 20);
            let duration = Duration::hours(3) + Duration::minutes(59);
            let range = TimeSpan::from_duration(start, duration).unwrap();
            assert_eq!(range.end().weekday, Weekday::Sun);
            assert_eq!(range.end() - range.start(), duration);

            let start = wt();
            let duration = Duration::zero();
            assert!(
                TimeSpan::from_duration(start, duration).is_none(),
                "it should fail if duration is zero"
            );

            let start = wt();
            let duration = Duration::minutes(-30);
            assert!(
                TimeSpan::from_duration(start, duration).is_none(),
                "it should fail if duration is negative"
            );

            let start = wt_with(Weekday::Sat, 0);
            let duration = Duration::days(2);
            assert!(
                TimeSpan::from_duration(start, duration).is_none(),
                "it should fail if duration is next week (> 1 day)"
            );

            let start = wt_with(Weekday::Sun, 20);
            let duration = Duration::hours(5);
            assert!(
                TimeSpan::from_duration(start, duration).is_none(),
                "it should fail if duration is next week (< 1 day)"
            );

            let start = wt_with(Weekday::Sun, 20);
            let duration = Duration::hours(4);
            assert!(
                TimeSpan::from_duration(start, duration).is_none(),
                "it should fail if duration is next week (even at 0)",
            );
        }

        #[test]
        fn test_intersects() {
            let start = WeekTime::new(Weekday::Tue, 12, 0).unwrap();
            let end = WeekTime::new(Weekday::Thu, 12, 0).unwrap();
            let range = TimeSpan(start, end);

            // f:  [-----]  (-----)
            let start = WeekTime::new(Weekday::Mon, 0, 0).unwrap();
            let end = WeekTime::new(Weekday::Tue, 10, 30).unwrap();
            let r = TimeSpan(start, end);
            assert!(!range.intersects(&r));
            assert!(!r.intersects(&range));

            // f:  [-----](-----)
            let start = WeekTime::new(Weekday::Mon, 0, 0).unwrap();
            let end = WeekTime::new(Weekday::Tue, 12, 0).unwrap();
            let r = TimeSpan(start, end);
            assert!(!range.intersects(&r));
            assert!(!r.intersects(&range));

            // t:  [---(-]---)
            let start = WeekTime::new(Weekday::Mon, 0, 0).unwrap();
            let end = WeekTime::new(Weekday::Tue, 13, 0).unwrap();
            let r = TimeSpan(start, end);
            assert!(range.intersects(&r));
            assert!(r.intersects(&range));

            // t: [--(-----)-]
            let start = WeekTime::new(Weekday::Mon, 0, 0).unwrap();
            let end = WeekTime::new(Weekday::Thu, 14, 0).unwrap();
            let r = TimeSpan(start, end);
            assert!(range.intersects(&r));
            assert!(r.intersects(&range));
        }
    }
}
