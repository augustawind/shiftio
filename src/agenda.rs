pub use chrono::Weekday;
use indexmap::IndexMap;
pub use time::Duration;

pub use crate::timetable::{TimeRange, Timetable, WeekTime};

/// Represents all the time ranges and requirements for a Project.
/// Time ranges must be non-overlapping - this is handled by the add methods.
pub struct Agenda {
    // A mapping of start times to `TimeBlock` objects.
    // The key for each `TimeBlock` is its start time.
    blocks: IndexMap<WeekTime, TimeBlock>,
}

impl Timetable<TimeBlock> for Agenda {
    fn ranges(&self) -> &IndexMap<WeekTime, TimeBlock> {
        &self.blocks
    }

    fn ranges_mut(&mut self) -> &mut IndexMap<WeekTime, TimeBlock> {
        &mut self.blocks
    }
}

impl Agenda {
    /// Return a new, empty Agenda.
    pub fn new() -> Self {
        let blocks = IndexMap::new();
        Agenda { blocks }
    }
}

/// Represents a block of time and its requirements in an Agenda.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeBlock {
    start: WeekTime,
    end: WeekTime,

    // Minimum number of workers needed during this block.
    min_workers: u32,
}

impl TimeRange for TimeBlock {
    fn start(&self) -> WeekTime {
        self.start
    }
    fn end(&self) -> WeekTime {
        self.end
    }
}

impl TimeBlock {
    /// Return a new TimeBlock with the given `start` and `end`.
    ///
    /// Returns [`None`] if `min_workers` is < 1, or if `end` is not after `start`.
    pub fn new(start: WeekTime, end: WeekTime, min_workers: u32) -> Option<Self> {
        let (start, end) = Self::init_pair(start, end)?;
        Self::_new(start, end, min_workers)
    }

    /// Return a new TimeBlock with the given `start`, where `end` is determined by `duration`.
    ///
    /// Returns [`None`] if `min_workers` is < 1, or if the the calculated end time is invalid.
    pub fn from_duration(start: WeekTime, duration: Duration, min_workers: u32) -> Option<Self> {
        let (start, end) = Self::init_duration(start, duration)?;
        Self::_new(start, end, min_workers)
    }

    fn _new(start: WeekTime, end: WeekTime, min_workers: u32) -> Option<Self> {
        if min_workers < 1 {
            return None;
        }
        Some(TimeBlock {
            start,
            end,
            min_workers,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use chrono::Weekday;

    fn tblock(day0: Weekday, hour0: u32, day1: Weekday, hour1: u32) -> TimeBlock {
        TimeBlock::new(
            WeekTime::new(day0, hour0, 0).unwrap(),
            WeekTime::new(day1, hour1, 0).unwrap(),
            1,
        )
        .unwrap()
    }

    mod test_agenda {
        use super::*;
        use Weekday::*;

        fn def_blocks() -> (TimeBlock, TimeBlock, TimeBlock, TimeBlock, TimeBlock) {
            (
                tblock(Mon, 10, Tue, 2),
                tblock(Tue, 2, Tue, 12),
                tblock(Wed, 0, Wed, 8),
                tblock(Wed, 14, Fri, 22),
                tblock(Sun, 0, Sun, 12),
            )
        }

        #[test]
        fn test_add_range() {
            let mut agenda = Agenda::new();
            let (block1, block2, block3, block4, block5) = def_blocks();
            let (b1, b2, b3, b4, b5) = def_blocks();

            assert!(agenda.add_range(block4).is_ok());
            assert_eq!(
                agenda.ranges().keys().collect::<Vec<&WeekTime>>(),
                vec![&b4.start()],
            );

            assert!(agenda.add_range(block1).is_ok());
            assert_eq!(
                agenda.ranges().keys().collect::<Vec<&WeekTime>>(),
                vec![&b1.start(), &b4.start()],
            );

            assert!(agenda.add_range(block2).is_ok());
            assert!(agenda.add_range(block5).is_ok());
            assert!(agenda.add_range(block3).is_ok());
            assert_eq!(
                agenda.ranges().values().collect::<Vec<&TimeBlock>>(),
                vec![&b1, &b2, &b3, &b4, &b5],
            );

            let overlap_b1_b2 = tblock(Mon, 20, Tue, 3);
            assert_eq!(
                agenda.add_range(overlap_b1_b2),
                Err(vec![b1, b2]),
                "if the block overlaps, an error with overlapping blocks should be returned",
            );
            let overlap_b3 = tblock(Wed, 0, Wed, 1);
            assert_eq!(agenda.add_range(overlap_b3), Err(vec![b3]));
        }

        #[test]
        fn test_add_ranges() {
            let mut agenda = Agenda::new();
            let (block1, block2, block3, block4, block5) = def_blocks();
            let (b1, b2, b3, b4, b5) = def_blocks();

            assert!(agenda
                .add_ranges(vec![block2, block1, block5, block3, block4])
                .is_ok());
            assert_eq!(
                agenda.ranges().values().collect::<Vec<&TimeBlock>>(),
                vec![&b1, &b2, &b3, &b4, &b5],
            );

            let b0 = tblock(Mon, 0, Mon, 4);
            let b6 = tblock(Sun, 12, Sun, 18);
            let overlap_b2_b3 = tblock(Tue, 3, Wed, 1);
            let overlap_b3_b4 = tblock(Wed, 2, Thu, 9);
            assert_eq!(
                agenda.add_ranges(vec![b0, overlap_b3_b4.clone(), overlap_b2_b3, b6]),
                Err((1, overlap_b3_b4, vec![b3.clone(), b4.clone()])),
                "if block(s) are overlapping, an error with the first should be returned",
            );
            assert_eq!(
                agenda.ranges().values().collect::<Vec<&TimeBlock>>(),
                vec![&b1, &b2, &b3, &b4, &b5],
                "no blocks should be added if any were overlapping",
            );
        }

        #[test]
        fn test_rm_range() {
            let mut agenda = Agenda::new();
            let (_, block2, _, block4, block5) = def_blocks();
            let (_, b2, _, b4, _) = def_blocks();

            agenda.add_range(block2).unwrap();
            agenda.add_range(block4).unwrap();
            assert_eq!(agenda.rm_range(b2.start()), Some(b2.clone()));
            assert_eq!(
                agenda.ranges().values().collect::<Vec<&TimeBlock>>(),
                vec![&b4],
            );

            assert_eq!(agenda.rm_range(block5.start()), None);
            assert_eq!(
                agenda.ranges().values().collect::<Vec<&TimeBlock>>(),
                vec![&b4],
                "if rm_range() doesn't find anything, nothing should be changed",
            );
        }
    }
}
