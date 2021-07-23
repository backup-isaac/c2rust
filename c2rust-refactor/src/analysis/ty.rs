// ty might be a bad name for this module. Fix?

use rustc::hir::def_id::DefId;
use rustc::hir::{ForeignItemKind, ImplItemKind, ItemKind, map, Node, TraitItemKind};
use rustc_index::vec::Idx;

/// Check if a definition is a `fn` item of some sort.  Note that this does not return true on
/// closures.
pub fn is_fn(hir_map: &map::Map, def_id: DefId) -> bool {
    let n = match hir_map.get_if_local(def_id) {
        None => return false,
        Some(n) => n,
    };

    match n {
        Node::Item(i) => match i.kind {
            ItemKind::Fn(..) => true,
            _ => false,
        },
        Node::ForeignItem(i) => match i.kind {
            ForeignItemKind::Fn(..) => true,
            _ => false,
        },
        Node::TraitItem(i) => match i.kind {
            TraitItemKind::Method(..) => true,
            _ => false,
        },
        Node::ImplItem(i) => match i.kind {
            ImplItemKind::Method(..) => true,
            _ => false,
        },
        _ => false,
    }
}

/// A variable index.
///
/// There are multiple kinds of variables using the same index type, so the variable kind must be
/// known by other means to use this effectively.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Var(pub u32);

impl Idx for Var {
    fn new(idx: usize) -> Var {
        assert!(idx as u32 as usize == idx);
        Var(idx as u32)
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

impl Var {
    pub fn next(self) -> Self {
        Var(self.0 + 1)
    }
}
