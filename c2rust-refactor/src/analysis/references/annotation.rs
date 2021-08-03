use std::collections::HashMap;

use arena::SyncDroplessArena;
use rustc::hir::def_id::DefId;
use rustc::ty::{Ty, TyCtxt, TyKind};
use syntax::ast::{LitKind, MetaItem, NestedMetaItem};

use crate::analysis::attr::{AttrVisitor, meta_item_list};
use crate::analysis::labeled_ty::LabeledTyCtxt;
use crate::ast_manip::Visit;
use crate::command::CommandState;
use crate::RefactorCtxt;

use super::RefdTy;

fn nested_bool(nmeta: &NestedMetaItem) -> Result<bool, &'static str> {
    match nmeta {
        NestedMetaItem::Literal(ref lit) => match lit.kind {
            LitKind::Bool(b) => Ok(b),
            _ => Err("expected bool"),
        },
        _ => Err("expected bool"),
    }
}

fn parse_reference_likes(meta: &MetaItem) -> Result<Box<[bool]>, &'static str> {
    meta_item_list(meta)?.iter()
        .map(|arg| nested_bool(arg))
        .collect()
}

pub fn handle_attrs<'a, 'tcx, 'lty>(
    tcx: TyCtxt<'tcx>,
    arena: &'lty SyncDroplessArena,
    st: &CommandState,
    dcx: &RefactorCtxt<'a, 'tcx>,
) -> (
    HashMap<DefId, RefdTy<'lty, 'tcx>>, // statics
    HashMap<DefId, &'lty [RefdTy<'lty, 'tcx>]>, // functions
) {
    let krate = st.krate();
    let mut v = AttrVisitor {
        def_attrs: Vec::new(),
    };
    krate.visit(&mut v);

    let mut statics = HashMap::new();
    let mut functions = HashMap::new();

    let lcx = LabeledTyCtxt::new(arena);

    for (node_id, attrs) in v.def_attrs {
        let def_id = if let Some(def_id) = dcx.hir_map().opt_local_def_id_from_node_id(node_id) {
            def_id
        } else {
            continue
        };

        for attr in attrs {
            let meta = if let Some(meta) = attr.meta() {
                meta
            } else {
                continue
            };

            if attr.name_or_empty().as_str() != "reference_like" {
                continue;
            }

            let reference_likes = parse_reference_likes(&meta).unwrap_or_else(|e| {
                panic!("bad #[reference_like] for {:?}: {}", def_id, e)
            });

            debug!("{} ref_likes: {:?}", tcx.def_path_str(def_id), reference_likes);
            let mut iter = reference_likes.into_iter();
            let mut labeler = |ty: Ty<'tcx>| match ty.kind {
                TyKind::RawPtr(_) => Some(*iter.next().unwrap_or_else(|| panic!("not enough labels"))),
                _ => None,
            };

            let ty = tcx.type_of(def_id);
            if let TyKind::FnDef(_, _) = ty.kind {
                let sig = tcx.fn_sig(def_id);
                let sig_ltys = sig.skip_binder().inputs_and_output.iter()
                    .map(|ty| lcx.label(ty, &mut labeler))
                    .collect::<Vec<_>>();
                if functions.insert(def_id, lcx.mk_slice(&sig_ltys)).is_some() {
                    panic!("duplicate #[reference_like] for {:?}", def_id);
                }
            } else {
                let lty = lcx.label(ty, &mut labeler);
                if statics.insert(def_id, lty).is_some() {
                    panic!("duplicate #[reference_like] for {:?}", def_id);
                }
            }
        }
    }

    (statics, functions)
}
