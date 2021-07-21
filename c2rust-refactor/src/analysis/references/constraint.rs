use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::hash::Hash;

use rustc::hir::def_id::DefId;
use rustc::mir::*;

use log::Level;
/// Associates `Place`s corresponding to local variables with the DefId
/// of the function in which they were defined.
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd)]
pub struct QualifiedPlace<'tcx>(Place<'tcx>, Option<DefId>);

impl<'tcx> QualifiedPlace<'tcx> {
    pub fn new(place: Place<'tcx>, func: Option<DefId>) -> QualifiedPlace<'tcx> {
        // It would probably be better to enforce this at compile time,
        // but doing so would add the boilerplate of reinventing Place
        if let PlaceBase::Local(_) = place.base {
            QualifiedPlace(place, Some(func.expect("local must be associated with a function def ID")))
        } else {
            QualifiedPlace(place, None)
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Constraint<'tcx> {
    pub from: QualifiedPlace<'tcx>,
    pub to: QualifiedPlace<'tcx>,
}

// unsure if I will keep this
/// Might be useful to show the programmer what is preventing conversion to reference
#[derive(Debug, PartialEq, PartialOrd)]
pub enum Taint<'tcx> {
    UsedInArithmetic,
    UsedInPtrCast,
    PassedToKnownTaintedFn(DefId),
    PassedToOpaqueFnPointer(QualifiedPlace<'tcx>),
    PassedToExternFn(DefId),
}

pub struct Constraints<'tcx> {
    pub edges: HashSet<Constraint<'tcx>>,
    taints: HashMap<QualifiedPlace<'tcx>, Taint<'tcx>>,
}

impl<'tcx> Constraints<'tcx> {
    pub fn new() -> Constraints<'tcx> {
        Constraints {
            edges: HashSet::new(),
            taints: HashMap::new(),
        }
    }

    pub fn add_taint(&mut self, place: QualifiedPlace<'tcx>, reason: Taint<'tcx>) {
        debug!("taint {:?} = {:?}", place, reason);
        match self.taints.entry(place) {
            Entry::Vacant(e) => {
                e.insert(reason);
            },
            Entry::Occupied(mut e) => if reason < *e.get() {
                e.insert(reason);
            },
        }
    }

    pub fn debug_constraints(&self) {
        debug!("edges: [");
        if log_enabled!(Level::Debug) {
            for edge in self.edges.iter() {
                debug!("    {:?}", edge);
            }
        }
        debug!("]");
        debug!("taints: [");
        if log_enabled!(Level::Debug) {
            for taint in self.taints.iter() {
                debug!("    {:?}", taint);
            }
        }
        debug!("]");
    }
}
