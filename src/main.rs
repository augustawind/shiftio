use chrono::{DateTime, Datelike, Timelike, Utc};
use indexmap::IndexMap;
use time::Duration;

/// Represents a non-zero range of time with a start and end.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeRange {
    start: DateTime<Utc>,
    end: DateTime<Utc>,
}

impl TimeRange {
    /// Create a new TimeRange from absolute start and end times.
    /// Returns [`None`] if `end` is not later than `start`.
    pub fn new(start: DateTime<Utc>, end: DateTime<Utc>) -> Option<Self> {
        if end <= start {
            return None;
        }
        Some(TimeRange { start, end })
    }

    /// Create a new TimeRange from a start time and a duration.
    /// Returns [`None`] if `duration` is zero or negative.
    pub fn from_duration(start: DateTime<Utc>, duration: Duration) -> Option<Self> {
        if duration <= Duration::zero() {
            return None;
        }
        let end = start + duration;
        Some(TimeRange { start, end })
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
    blocks: IndexMap<DateTime<Utc>, Timeblock>,
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
            .insert(range.start.clone(), Timeblock { range, min_agents });
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

fn main() {
    println!("Hello, world!");
}
