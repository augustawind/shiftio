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
    /// Returns [`None`] if `duration` is zero or negative.
    pub fn from_duration(start: WeekTime, duration: Duration) -> Option<Self> {
        // TODO: insert these debug stmts into actual errors in a Result.

        // Assert duration is greater than zero.
        if duration <= Duration::zero() {
            eprintln!("Duration is <= zero.");
            return None;
        }

        // Assert duration is not longer than remaining time in week.
        let days_left = 6 - start.weekday.num_days_from_monday() as i64;
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
                let time_left = start.time - Duration::hours(24);
                if duration.num_seconds() > time_left.num_seconds_from_midnight() as i64 {
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

/// Manages a Timetable and a Roster of Agents that can fulfill it.
pub struct Schedule {
    timetable: Timetable,
    roster: Roster,
}

impl Schedule {
    pub fn new(timetable: Timetable, roster: Roster) -> Self {
        Self { timetable, roster }
    }
}

/// Represents all the time ranges and requirements for a Schedule.
/// Time ranges must be non-overlapping - this is handled by the add methods.
pub struct Timetable {
    // A mapping of start times to `Timeblock` objects.
    // The key for each `Timeblock` is its start time.
    blocks: IndexMap<WeekTime, Timeblock>,
}

impl Timetable {
    pub fn new() -> Self {
        let blocks = IndexMap::new();
        Self { blocks }
    }

    /// Add a time range to the Timetable.
    /// If `range` overlaps with any ranges already in the Timetable, an Err is returned with a
    /// vector of all the ranges that intersect with `range`, in ascending order.
    pub fn add_time(&mut self, range: TimeRange, min_agents: u32) -> Result<(), Vec<TimeRange>> {
        let overlapping: Vec<TimeRange> = self
            .blocks
            .values()
            .filter_map(|block| {
                if range.intersects(&block.range) {
                    Some(block.range.clone())
                } else {
                    None
                }
            })
            .collect();
        if !overlapping.is_empty() {
            return Err(overlapping);
        }

        self.blocks
            .insert(range.start, Timeblock { range, min_agents });
        self.blocks.sort_keys();

        Ok(())
    }
}

/// Represents a block of time and its requirements in a Timetable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Timeblock {
    // The time range covered by this block.
    pub range: TimeRange,
    // Minimum number of agents needed during this block.
    pub min_agents: u32,
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

    // fn dt() -> DateTime<Utc> {
    //     Utc.ymd(1991, 11, 14).and_hms(16, 34, 0)
    // }

    fn wt() -> WeekTime {
        WeekTime::from_time(Weekday::Thu, NaiveTime::from_hms(11, 22, 33)).unwrap()
    }

    mod test_time_range {
        use super::*;

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
            let start = wt();
            let duration = Duration::hours(8);
            let range = TimeRange::from_duration(start, duration).unwrap();
            assert!(range.end() - range.start() == Duration::hours(8));

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
}
