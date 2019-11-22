//! Utilities for creating optimal work schedules.
//!
//! This library relies heavily on the concept of a _week_ as a unit of time. A _week_ is defined
//! as a series of 7 _weekdays_ beginning with Monday and ending with Sunday. Weekdays are
//! represented by variants of the [`chrono::Weekday`] enum.

use std::cmp::Ordering;
use std::ops::{Add, Sub};

use chrono::{DateTime, Datelike, NaiveTime, TimeZone, Timelike, Utc, Weekday};
use indexmap::IndexMap;
use time::Duration;

const DUMMY_YEAR: i32 = 1970;
const DUMMY_WEEK: u32 = 1;

/// Represents a naive time on a day of the week.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WeekTime {
    weekday: Weekday,
    time: NaiveTime,
    datetime: DateTime<Utc>,
}

impl PartialOrd for WeekTime {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.datetime.partial_cmp(&other.dt())
    }
}

impl Ord for WeekTime {
    fn cmp(&self, other: &Self) -> Ordering {
        self.datetime.cmp(&other.dt())
    }
}

impl WeekTime {
    /// Create a new `WeekTime` from a weekday, an hour, and a minute.
    pub fn new(weekday: Weekday, hour: u32, min: u32) -> Option<Self> {
        let time = NaiveTime::from_hms_opt(hour, min, 0)?;
        let datetime = Self::dt_from_weekday_and_time(weekday, time).unwrap();
        Some(WeekTime {
            weekday,
            time,
            datetime,
        })
    }

    /// Create a new `WeekTime` from a weekday and a naive time.
    pub fn from_time(weekday: Weekday, time: NaiveTime) -> Option<Self> {
        let datetime = Self::dt_from_weekday_and_time(weekday, time)?;
        Some(WeekTime {
            weekday,
            time,
            datetime,
        })
    }

    fn dt_from_weekday_and_time(weekday: Weekday, time: NaiveTime) -> Option<DateTime<Utc>> {
        Utc.isoywd(DUMMY_YEAR, DUMMY_WEEK, weekday).and_time(time)
    }

    pub fn dt(&self) -> DateTime<Utc> {
        self.datetime
    }

    /// Returns the number of days from `self.weekday` to the end of the week.
    /// Sunday is considered the end of the week. The result will be a uint in the range `[0..6]`,
    /// e.g. if `self.weekday` is Sunday this function will return `0`.
    pub fn days_left_in_week(&self) -> u32 {
        6 - self.weekday.num_days_from_monday()
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
        let datetime = self.datetime + duration;
        WeekTime {
            weekday: datetime.weekday(),
            time: datetime.time(),
            datetime,
        }
    }
}

impl Sub<Duration> for WeekTime {
    type Output = Self;

    fn sub(self, duration: Duration) -> Self {
        let datetime = self.datetime - duration;
        WeekTime {
            weekday: datetime.weekday(),
            time: datetime.time(),
            datetime,
        }
    }
}

impl Sub<WeekTime> for WeekTime {
    type Output = Duration;

    fn sub(self, weektime: WeekTime) -> Duration {
        self.datetime - weektime.datetime
    }
}

/// Represents a non-zero range of time with a start and end.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeRange {
    start: WeekTime,
    end: WeekTime,
}

impl TimeRange {
    /// Create a new TimeRange from start and end times.
    /// Returns [`None`] if `end` is not later than `start`.
    pub fn new(start: WeekTime, end: WeekTime) -> Option<Self> {
        if end <= start {
            return None;
        }
        Some(TimeRange { start, end })
    }

    /// Create a new TimeRange from a start time and a duration.
    ///
    /// Calculates the end time by adding the duration to the start time. Returns [`None`] if
    /// `duration` is zero or negative, or if the end time would be in a different week (weeks start
    /// on Monday and end on Sunday). For example, if `start` is on a Friday and `duration` is 3
    /// days, the end time would be on Monday of next week, so [`None`] would be returned.
    pub fn from_duration(start: WeekTime, duration: Duration) -> Option<Self> {
        // TODO: insert these debug stmts into actual errors in a Result.

        // Assert duration is greater than zero.
        if duration <= Duration::zero() {
            eprintln!("Duration is <= zero.");
            return None;
        }

        // Assert duration is not longer than remaining time in week.
        let days_left = start.days_left_in_week() as i64;
        match duration.num_days().cmp(&days_left) {
            Ordering::Greater => {
                eprintln!(
                    "Duration is {} days, but only {} day(s) are left in the week (from {:?}).",
                    duration.num_days(),
                    days_left,
                    start.weekday,
                );
                return None;
            }
            Ordering::Equal => {
                let time_left = start.seconds_until_tomorrow() as i64;
                if duration.num_seconds() > time_left {
                    eprintln!(
                        "Duration is {} seconds ({} minutes) past the end of the week.",
                        duration.num_seconds(),
                        duration.num_minutes(),
                    );
                    return None;
                }
            }
            _ => (),
        };

        let end = start + duration;
        Some(TimeRange { start, end })
    }

    /// Returns the lower boundary the TimeRange.
    pub fn start(&self) -> WeekTime {
        self.start
    }

    /// Returns the upper boundary the TimeRange.
    pub fn end(&self) -> WeekTime {
        self.end
    }

    /// Returns `true` if this `TimeRange` and the given `range` overlap.
    pub fn intersects(&self, range: &TimeRange) -> bool {
        range.start < self.end && range.end > self.start
    }
}

/// Manages a Schedule and a Roster of Agents that can fulfill it.
pub struct Coordinator {
    timetable: Schedule,
    roster: Roster,
}

impl Coordinator {
    pub fn new(timetable: Schedule, roster: Roster) -> Self {
        Self { timetable, roster }
    }
}

trait TimeSpan {
    fn range(&self) -> &TimeRange;
}

trait Timetable<T: TimeSpan> {
    fn times(&self) -> &IndexMap<WeekTime, T>;
    fn add_time(&mut self, time: T) -> Result<(), Vec<T>>;
    fn add_times<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), (usize, T, Vec<T>)>;
    fn rm_time(&mut self, start: &WeekTime) -> Option<T>;
}

/// Represents all the time ranges and requirements for a Coordinator.
/// Time ranges must be non-overlapping - this is handled by the add methods.
pub struct Schedule {
    // A mapping of start times to `TimeBlock` objects.
    // The key for each `TimeBlock` is its start time.
    blocks: IndexMap<WeekTime, TimeBlock>,
}

impl Schedule {
    /// Return a new, empty Schedule.
    pub fn new() -> Self {
        let blocks = IndexMap::new();
        Self { blocks }
    }

    // Return a list of all time blocks in `self.blocks` that overlap with `time_block`.
    fn find_overlapping(&self, time_block: &TimeBlock) -> Vec<TimeBlock> {
        self.blocks
            .values()
            .filter_map(|block| {
                if time_block.range.intersects(&block.range) {
                    Some(block.clone())
                } else {
                    None
                }
            })
            .collect()
    }
}

impl Timetable<TimeBlock> for Schedule {
    fn times(&self) -> &IndexMap<WeekTime, TimeBlock> {
        &self.blocks
    }

    /// Add a [`TimeBlock`] to the Schedule.
    ///
    /// If the time block overlaps with any blocks in the Schedule, an Err is returned with a vector
    /// of all the time blocks it overlapped in ascending order.
    fn add_time(&mut self, block: TimeBlock) -> Result<(), Vec<TimeBlock>> {
        let overlapping = self.find_overlapping(&block);
        if !overlapping.is_empty() {
            return Err(overlapping);
        }

        self.blocks.insert(block.range.start, block);
        self.blocks.sort_keys();

        Ok(())
    }

    /// Add multiple [`TimeBlock`]s to the Schedule.
    ///
    /// If any time blocks in `iter` overlap with any blocks in the Schedule, an Err is returned
    /// with a tuple of `(index, block, overlapping)`, where `block` is the first block in `iter`
    /// that overlapped, `index` is its index in `iter`, and `overlapping` is a vector of all
    /// the blocks it overlapped in the Schedule in ascending order. Note that this includes
    /// duplicates as well.
    ///
    /// This is more efficient than calling [`add_time`] individually for each time block.
    fn add_times<T: IntoIterator<Item = TimeBlock>>(
        &mut self,
        iter: T,
    ) -> Result<(), (usize, TimeBlock, Vec<TimeBlock>)> {
        let mut blocks = Vec::new();

        for (i, block) in iter.into_iter().enumerate() {
            let overlapping = self.find_overlapping(&block);
            if !overlapping.is_empty() {
                return Err((i, block, overlapping));
            }
            blocks.push((block.range.start, block));
        }

        self.blocks.extend(blocks);
        self.blocks.sort_keys();
        Ok(())
    }

    /// Remove a time block from the Schedule.
    ///
    /// Returns the [`TimeBlock`], or [`None`] if no block exists with the given `start_time`.
    fn rm_time(&mut self, start_time: &WeekTime) -> Option<TimeBlock> {
        self.blocks.shift_remove(start_time)
    }
}

/// Represents a block of time and its requirements in a Schedule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeBlock {
    // The time range covered by this block.
    range: TimeRange,
    // Minimum number of agents needed during this block.
    min_agents: u32,
}

impl TimeBlock {
    /// Return a new TimeBlock.
    ///
    /// Returns [`None`] if `min_agents` is < 1.
    pub fn new(range: TimeRange, min_agents: u32) -> Option<Self> {
        if min_agents < 1 {
            return None;
        }
        Some(TimeBlock { range, min_agents })
    }
}

impl TimeSpan for TimeBlock {
    fn range(&self) -> &TimeRange {
        &self.range
    }
}

/// A collection of Agents.
pub struct Roster {
    // A mapping of Agents by their names.
    agents: IndexMap<String, Agent>,
}

/// Represents the availability and needs of a worker in the system.
pub struct Agent {
    // A unique identifier for this Agent.
    name: String,
    // Time ranges this Agent is available.
    availability: Vec<TimeRange>,
    // Time needed by this Agent, in minutes.
    time_needed: u32,
}

#[cfg(test)]
mod test {
    use super::*;

    mod utils {
        use crate::{TimeBlock, TimeRange, WeekTime, Weekday};

        pub fn wt() -> WeekTime {
            wt_with(Weekday::Thu, 11)
        }

        pub fn wt_with(weekday: Weekday, hour: u32) -> WeekTime {
            WeekTime::new(weekday, hour, 0).unwrap()
        }

        pub fn trange(day0: Weekday, hour0: u32, day1: Weekday, hour1: u32) -> TimeRange {
            TimeRange::new(wt_with(day0, hour0), wt_with(day1, hour1)).unwrap()
        }

        pub fn tblock(range: TimeRange) -> TimeBlock {
            TimeBlock::new(range, 1).unwrap()
        }
    }

    mod test_time_range {
        use super::*;
        use utils::*;

        #[test]
        fn test_new() {
            let start = wt();
            let end = wt() + Duration::hours(8);
            let range = TimeRange::new(start, end).unwrap();
            assert!(range.end() - range.start() == Duration::hours(8));

            let start = wt();
            let end = start;
            assert!(
                TimeRange::new(start, end).is_none(),
                "it should fail if start == end"
            );

            let start = wt();
            let end = start - Duration::hours(1);
            assert!(
                TimeRange::new(start, end).is_none(),
                "it should fail if start > end"
            );
        }

        #[test]
        fn test_from_duration() {
            // happy path
            let start = wt();
            let duration = Duration::hours(8);
            let range = TimeRange::from_duration(start, duration).unwrap();
            assert_eq!(range.end() - range.start(), Duration::hours(8));

            // happy path (maximum possible duration)
            let start = wt_with(Weekday::Sun, 20);
            let duration = Duration::hours(4);
            let range = TimeRange::from_duration(start, duration).unwrap();
            assert_eq!(range.end.weekday, Weekday::Mon);
            assert_eq!(range.end.time.num_seconds_from_midnight(), 0);
            assert_eq!(range.end - range.start, Duration::hours(4));

            let start = wt();
            let duration = Duration::zero();
            assert!(
                TimeRange::from_duration(start, duration).is_none(),
                "it should fail if duration is zero"
            );

            let start = wt();
            let duration = Duration::minutes(-30);
            assert!(
                TimeRange::from_duration(start, duration).is_none(),
                "it should fail if duration is negative"
            );

            let start = wt_with(Weekday::Sat, 0);
            let duration = Duration::days(2);
            assert!(
                TimeRange::from_duration(start, duration).is_none(),
                "it should fail if duration is next week (> 1 day)"
            );

            let start = wt_with(Weekday::Sun, 20);
            let duration = Duration::hours(5);
            assert!(
                TimeRange::from_duration(start, duration).is_none(),
                "it should fail if duration is next week (< 1 day)"
            );
        }

        #[test]
        fn test_intersects() {
            let start = WeekTime::new(Weekday::Tue, 12, 0).unwrap();
            let end = WeekTime::new(Weekday::Thu, 12, 0).unwrap();
            let range = TimeRange::new(start, end).unwrap();

            // f:  [-----]  (-----)
            let start = WeekTime::new(Weekday::Mon, 0, 0).unwrap();
            let end = WeekTime::new(Weekday::Tue, 10, 30).unwrap();
            let r = TimeRange::new(start, end).unwrap();
            assert!(!range.intersects(&r));
            assert!(!r.intersects(&range));

            // f:  [-----](-----)
            let start = WeekTime::new(Weekday::Mon, 0, 0).unwrap();
            let end = WeekTime::new(Weekday::Tue, 12, 0).unwrap();
            let r = TimeRange::new(start, end).unwrap();
            assert!(!range.intersects(&r));
            assert!(!r.intersects(&range));

            // t:  [---(-]---)
            let start = WeekTime::new(Weekday::Mon, 0, 0).unwrap();
            let end = WeekTime::new(Weekday::Tue, 13, 0).unwrap();
            let r = TimeRange::new(start, end).unwrap();
            assert!(range.intersects(&r));
            assert!(r.intersects(&range));

            // t: [--(-----)-]
            let start = WeekTime::new(Weekday::Mon, 0, 0).unwrap();
            let end = WeekTime::new(Weekday::Thu, 14, 0).unwrap();
            let r = TimeRange::new(start, end).unwrap();
            assert!(range.intersects(&r));
            assert!(r.intersects(&range));
        }
    }

    mod test_schedule {
        use super::*;
        use utils::*;

        use Weekday::*;

        fn def_blocks() -> (TimeBlock, TimeBlock, TimeBlock, TimeBlock, TimeBlock) {
            (
                tblock(trange(Mon, 10, Tue, 2)),
                tblock(trange(Tue, 2, Tue, 12)),
                tblock(trange(Wed, 0, Wed, 8)),
                tblock(trange(Wed, 14, Fri, 22)),
                tblock(trange(Sun, 0, Sun, 12)),
            )
        }

        #[test]
        fn test_add_time() {
            let mut schedule = Schedule::new();
            let (block1, block2, block3, block4, block5) = def_blocks();
            let (b1, b2, b3, b4, b5) = def_blocks();

            assert!(schedule.add_time(block4).is_ok());
            assert_eq!(
                schedule.times().keys().collect::<Vec<&WeekTime>>(),
                vec![&b4.range.start],
            );

            assert!(schedule.add_time(block1).is_ok());
            assert_eq!(
                schedule.times().keys().collect::<Vec<&WeekTime>>(),
                vec![&b1.range.start, &b4.range.start],
            );

            assert!(schedule.add_time(block2).is_ok());
            assert!(schedule.add_time(block5).is_ok());
            assert!(schedule.add_time(block3).is_ok());
            assert_eq!(
                schedule.times().values().collect::<Vec<&TimeBlock>>(),
                vec![&b1, &b2, &b3, &b4, &b5],
            );

            let overlap_b1_b2 = tblock(trange(Mon, 20, Tue, 3));
            assert_eq!(
                schedule.add_time(overlap_b1_b2),
                Err(vec![b1, b2]),
                "if the block overlaps, an error with overlapping blocks should be returned",
            );
            let overlap_b3 = tblock(trange(Wed, 0, Wed, 1));
            assert_eq!(schedule.add_time(overlap_b3), Err(vec![b3]));
        }

        #[test]
        fn test_add_times() {
            let mut schedule = Schedule::new();
            let (block1, block2, block3, block4, block5) = def_blocks();
            let (b1, b2, b3, b4, b5) = def_blocks();

            assert!(schedule
                .add_times(vec![block2, block1, block5, block3, block4])
                .is_ok());
            assert_eq!(
                schedule.times().values().collect::<Vec<&TimeBlock>>(),
                vec![&b1, &b2, &b3, &b4, &b5],
            );

            let b0 = tblock(trange(Mon, 0, Mon, 4));
            let b6 = tblock(trange(Sun, 12, Sun, 18));
            let overlap_b2_b3 = tblock(trange(Tue, 3, Wed, 1));
            let overlap_b3_b4 = tblock(trange(Wed, 2, Thu, 9));
            assert_eq!(
                schedule.add_times(vec![b0, overlap_b3_b4.clone(), overlap_b2_b3, b6]),
                Err((1, overlap_b3_b4, vec![b3.clone(), b4.clone()])),
                "if block(s) are overlapping, an error with the first should be returned",
            );
            assert_eq!(
                schedule.times().values().collect::<Vec<&TimeBlock>>(),
                vec![&b1, &b2, &b3, &b4, &b5],
                "no blocks should be added if any were overlapping",
            );
        }

        #[test]
        fn test_rm_time() {
            let mut schedule = Schedule::new();
            let (_, block2, _, block4, block5) = def_blocks();
            let (_, b2, _, b4, _) = def_blocks();

            schedule.add_time(block2).unwrap();
            schedule.add_time(block4).unwrap();
            assert_eq!(schedule.rm_time(&b2.range.start), Some(b2.clone()));
            assert_eq!(
                schedule.times().values().collect::<Vec<&TimeBlock>>(),
                vec![&b4],
            );

            assert_eq!(schedule.rm_time(&block5.range.start), None);
            assert_eq!(
                schedule.times().values().collect::<Vec<&TimeBlock>>(),
                vec![&b4],
                "if rm_time() doesn't find anything, nothing should be changed",
            );
        }
    }
}
