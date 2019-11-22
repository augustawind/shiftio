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
    /// Returns a new, empty Roster.
    pub fn new() -> Self {
        let workers = HashMap::new();
        Roster { workers }
    }

    pub fn workers(&self) -> &HashMap<String, Worker> {
        &self.workers
    }

    /// Adds a worker to the Roster.
    ///
    /// Each worker's `name` must be unique in the Roster. If the worker's name is already in use,
    /// this method will fail and return an Err with a copy of the worker that is causing the
    /// conflict.
    pub fn add_worker(&mut self, worker: Worker) -> Result<(), Worker> {
        if let Some(other) = self.workers.get(&worker.name).cloned() {
            return Err(other);
        }
        self.workers.insert(worker.name.clone(), worker);
        Ok(())
    }

    /// Removes a worker from the Roster.
    ///
    /// Returns the removed worker, or [`None`] if there is none.
    pub fn rm_worker<T: ToString>(&mut self, name: T) -> Option<Worker> {
        self.workers.remove(&name.to_string())
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
    /// Returns a new Worker with the given parameters.
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

/// Represents a range of time that a Worker is available to work.
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

#[cfg(test)]
mod tests {
    use super::*;

    fn wk(name: &str) -> Worker {
        Worker::new(name, Duration::hours(40)).unwrap()
    }

    fn s(s: &str) -> String {
        s.to_string()
    }

    macro_rules! set {
        ($($elem:expr),* $(,)*) => {{
            let mut _set = ::std::collections::HashSet::new();
            $(
                _set.insert($elem);
            )*
            _set
        }}
    }

    mod test_roster {
        use super::*;
        use std::collections::HashSet;

        #[test]
        fn test_names_unique() {
            let mut roster = Roster::new();

            // populate the roster
            assert!(roster.add_worker(wk("bob")).is_ok());
            assert!(roster.add_worker(wk("steve")).is_ok());
            assert!(roster.add_worker(wk("jen")).is_ok());
            assert_eq!(
                roster
                    .workers()
                    .keys()
                    .cloned()
                    .collect::<HashSet<String>>(),
                set![s("bob"), s("steve"), s("jen")],
            );

            // try to add another steve
            assert_eq!(
                roster.add_worker(wk("steve")),
                Err(wk("steve")),
                "should return the dupe worker when adding a worker with the same name",
            );
            assert_eq!(
                roster
                    .workers()
                    .keys()
                    .cloned()
                    .collect::<HashSet<String>>(),
                set![s("bob"), s("steve"), s("jen")],
            );

            // remove steve and then add him back
            assert_eq!(roster.rm_worker("steve").unwrap(), wk("steve"));
            assert!(roster.add_worker(wk("steve")).is_ok());
            assert_eq!(
                roster
                    .workers()
                    .keys()
                    .cloned()
                    .collect::<HashSet<String>>(),
                set![s("bob"), s("steve"), s("jen")],
            );
        }
    }
}
