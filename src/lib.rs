//! Utilities for creating optimal work schedules.
//!
//! # Weeks
//!
//! This library relies heavily on the concept of a _week_ as a unit of time. A _week_ is defined
//! as a series of 7 _weekdays_ beginning with Monday and ending with Sunday. Weekdays are
//! represented by variants of the [`chrono::Weekday`] enum.
pub mod agenda;
pub mod timetable;
pub mod worker;

pub use chrono::Weekday;
pub use time::Duration;

pub use crate::agenda::Agenda;
pub use crate::timetable::{TimeRange, Timetable, WeekTime};
pub use crate::worker::Roster;

/// Manages an Agenda and a Roster of Workers that can fulfill it.
pub struct Project {
    agenda: Agenda,
    roster: Roster,
}

impl Project {
    pub fn new(agenda: Agenda, roster: Roster) -> Self {
        Project { agenda, roster }
    }
}
