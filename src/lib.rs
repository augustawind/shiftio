//! Utilities for creating optimal work schedules.
//!
//! This library relies heavily on the concept of a _week_ as a unit of time. A _week_ is defined
//! as a series of 7 _weekdays_ beginning with Monday and ending with Sunday. Weekdays are
//! represented by variants of the [`chrono::Weekday`] enum.
pub mod timetable;

use chrono::Timelike;
use indexmap::IndexMap;

use crate::timetable::{TimeRange, TimeSpan, Timetable, WeekTime};

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

        self.blocks.insert(block.range().start(), block);
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
            blocks.push((block.range().start(), block));
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

    use chrono::Weekday;

    fn trange(day0: Weekday, hour0: u32, day1: Weekday, hour1: u32) -> TimeRange {
        TimeRange::new(
            WeekTime::new(day0, hour0, 0).unwrap(),
            WeekTime::new(day1, hour1, 0).unwrap(),
        )
        .unwrap()
    }

    fn tblock(range: TimeRange) -> TimeBlock {
        TimeBlock::new(range, 1).unwrap()
    }

    mod test_schedule {
        use super::*;

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
                vec![&b4.range().start()],
            );

            assert!(schedule.add_time(block1).is_ok());
            assert_eq!(
                schedule.times().keys().collect::<Vec<&WeekTime>>(),
                vec![&b1.range().start(), &b4.range().start()],
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
            assert_eq!(schedule.rm_time(&b2.range().start()), Some(b2.clone()));
            assert_eq!(
                schedule.times().values().collect::<Vec<&TimeBlock>>(),
                vec![&b4],
            );

            assert_eq!(schedule.rm_time(&block5.range().start()), None);
            assert_eq!(
                schedule.times().values().collect::<Vec<&TimeBlock>>(),
                vec![&b4],
                "if rm_time() doesn't find anything, nothing should be changed",
            );
        }
    }
}
