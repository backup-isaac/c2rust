use std::collections::{HashMap, HashSet, VecDeque};
use std::collections::hash_map::Entry;
use std::hash::Hash;

use rustc::hir::def_id::DefId;
use rustc::mir::*;

use log::Level;
/// Associates `Place`s corresponding to local variables with the DefId
/// of the function in which they were defined.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd)]
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

    pub fn place(&self) -> &Place<'tcx> {
        &self.0
    }

    pub fn func(&self) -> Option<DefId> {
        self.1
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Constraint<'tcx> {
    pub from: QualifiedPlace<'tcx>,
    pub to: QualifiedPlace<'tcx>,
}

// unsure if I will keep this
/// Might be useful to show the programmer what is preventing conversion to reference
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Taint<'tcx> {
    UsedInArithmetic,
    // Cast to a pointer of another type, excluding `void *`
    UsedInPtrCast,
    PassedToKnownTaintedFn(DefId),
    PassedToOpaqueFnPointer(QualifiedPlace<'tcx>),
    PassedToExternFn(DefId),
    // Returned from a public function, exposed as a public global variable,
    // or as a public struct field
    ExposedPublicly(QualifiedPlace<'tcx>),
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

    pub fn add_taint(&mut self, place: QualifiedPlace<'tcx>, reason: Taint<'tcx>) -> bool {
        match self.taints.entry(place) {
            Entry::Vacant(e) => {
                e.insert(reason);
                true
            },
            Entry::Occupied(mut e) => if reason < *e.get() {
                e.insert(reason);
                true
            } else {
                false
            },
        }
    }

    pub fn solve(mut self) -> HashMap<QualifiedPlace<'tcx>, Taint<'tcx>> {
        let mut graph = HashMap::new();
        for constraint in self.edges.iter() {
            match graph.entry(constraint.from.clone()) {
                Entry::Vacant(e) => {
                    e.insert(vec![constraint.to.clone()]);
                },
                Entry::Occupied(mut e) => e.get_mut().push(constraint.to.clone()),
            }
        }

        let mut queue = self.taints.iter()
            .map(|(place, reason)| (place.clone(), reason.clone()))
            .collect::<VecDeque<_>>();
        while let Some((place, reason)) = queue.pop_front() {
            for succ in graph.get(&place).unwrap_or(&vec![]) {
                if self.add_taint(succ.clone(), reason.clone()) {
                    queue.push_back((succ.clone(), reason.clone()));
                }
            }
        }

        self.taints
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
