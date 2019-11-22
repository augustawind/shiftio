use std::collections::HashMap;

pub use chrono::Weekday;
use indexmap::IndexMap;
pub use time::Duration;

pub use crate::agenda::Agenda;
pub use crate::timetable::{TimeRange, Timetable, WeekTime};

/// A collection of Workers.
pub struct Roster {
    // A mapping of Workers by their names.
    workers: HashMap<String, Worker>,
}

impl Roster {
    pub fn new() -> Self {
        let workers = HashMap::new();
        Roster { workers }
    }

    pub fn add_worker(&mut self, worker: Worker) -> Result<(), Worker> {
        if let Some(other) = self.workers.get(&worker.name).cloned() {
            return Err(other);
        }
        self.workers.insert(worker.name.clone(), worker);
        Ok(())
    }
}

/// Represents the availability and needs of a worker in the system.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Worker {
    // A unique identifier for this Worker.
    name: String,
    // Time needed by this Worker, in minutes.
    hours_needed: Duration,
    // Time ranges this Worker is available.
    availability: IndexMap<WeekTime, Availability>,
}

impl Timetable<Availability> for Worker {
    fn ranges(&self) -> &IndexMap<WeekTime, Availability> {
        &self.availability
    }

    fn ranges_mut(&mut self) -> &mut IndexMap<WeekTime, Availability> {
        &mut self.availability
    }
}

impl Worker {
    pub fn new<T: ToString>(name: T, hours_needed: Duration) -> Option<Self> {
        // TODO: proper errors
        if hours_needed <= Duration::zero() {
            return None;
        }
        if hours_needed > Duration::weeks(1) {
            return None;
        }

        Some(Worker {
            name: name.to_string(),
            hours_needed: hours_needed,
            availability: IndexMap::new(),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Availability {
    start: WeekTime,
    end: WeekTime,
}

impl TimeRange for Availability {
    fn start(&self) -> WeekTime {
        self.start
    }
    fn end(&self) -> WeekTime {
        self.end
    }
}

impl Availability {
    /// Return a new Availability with the given `start` and `end`.
    ///
    /// Returns [`None`] if `end` is not after `start`.
    pub fn new(start: WeekTime, end: WeekTime) -> Option<Self> {
        let (start, end) = Self::init_pair(start, end)?;
        Self::_new(start, end)
    }

    /// Return a new Availability with the given `start`, where `end` is determined by `duration`.
    ///
    /// Returns [`None`] if the the calculated end time is invalid.
    pub fn from_duration(start: WeekTime, duration: Duration) -> Option<Self> {
        let (start, end) = Self::init_duration(start, duration)?;
        Self::_new(start, end)
    }

    fn _new(start: WeekTime, end: WeekTime) -> Option<Self> {
        Some(Availability { start, end })
    }
}
