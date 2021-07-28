// ty might be a bad name for this module. Fix?

use rustc::hir::def_id::DefId;
use rustc::hir::{ForeignItemKind, ImplItemKind, ItemKind, map, Node, TraitItemKind};
use rustc_index::vec::Idx;
use rustc::ty::{Ty, TyCtxt, TyKind};

use c2rust_ast_builder::IntoSymbol;

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

pub fn names_c_void<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    if let TyKind::Adt(adt, _) = ty.kind {
        let def_path = tcx.def_path(adt.did);

        if tcx.crate_name(def_path.krate) != "core".into_symbol() {
            return false;
        }

        return def_path.data.iter().map(|it| it.data.get_opt_name()).collect::<Vec<_>>()
            == ["ffi", "c_void"].iter().map(|s| Some(s.into_symbol())).collect::<Vec<_>>();
    }
    false
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
