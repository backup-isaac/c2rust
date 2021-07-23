use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

use arena::SyncDroplessArena;
use rustc::hir::def_id::{DefId, LOCAL_CRATE};
use rustc::mir::*;
use rustc::ty::{List, Ty, TyCtxt, TyKind};
use rustc_index::vec::IndexVec;
use rustc_target::abi::VariantIdx;
use syntax::source_map::{DUMMY_SP, Spanned};

use crate::analysis::labeled_ty::{FnSig, LabeledTyCtxt};

use super::{FunctionResult, RefLike, RefdTy};
use super::constraint::Constraints;
use super::func::FuncCtxt;

pub struct Ctxt<'lty, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub arena: &'lty SyncDroplessArena,
    pub constraints: Constraints<'tcx>,

    funcs: HashSet<DefId>,
    opaque_func_decls: HashSet<DefId>,
}

impl<'lty, 'a: 'lty, 'tcx: 'a> Ctxt<'lty, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        arena: &'lty SyncDroplessArena,
        funcs: HashSet<DefId>,
    ) -> Ctxt<'lty, 'tcx> {
        Ctxt {
            tcx,
            arena,
            constraints: Constraints::new(),
            funcs,
            opaque_func_decls: HashSet::new(),
        }
    }

    pub fn analyze_intra(&mut self) {
        let mut worklist = Vec::from_iter(self.funcs.iter().copied());
        while let Some(def_id) = worklist.pop() {
            let mir = self.tcx.optimized_mir(def_id);
            let mut func_cx = FuncCtxt::new(self, def_id, mir);

            let mut collected_def_ids = Vec::new();
            for (bbid, bb) in mir.basic_blocks().iter_enumerated() {
                if let Some(dependent_def_id) = func_cx.analyze_basic_block(bbid, bb) {
                    collected_def_ids.push(dependent_def_id);
                }
            }

            for dependent_def_id in collected_def_ids {
                if self.tcx.is_foreign_item(dependent_def_id)
                || dependent_def_id.krate != def_id.krate {
                    self.opaque_func_decls.insert(dependent_def_id);
                } else if self.funcs.insert(dependent_def_id) {
                    worklist.push(dependent_def_id);
                }
            }
        }
    }

    pub fn into_results(self) -> (
        HashMap<DefId, RefdTy<'lty, 'tcx>>, // statics
        HashMap<DefId, FunctionResult<'lty, 'tcx>> // functions
    ) {
        let Self {
            tcx,
            arena,
            constraints,
            funcs,
            opaque_func_decls
        } = self;

        let lcx = LabeledTyCtxt::new(arena);
        let mut functions = HashMap::new();
        let mut statics = HashMap::new();

        for &def_id in funcs.iter() {
            let sig = tcx.fn_sig(def_id);
            let mir = tcx.optimized_mir(def_id);
            let mut locals: IndexVec<Local, Spanned<RefdTy<'lty, 'tcx>>> = IndexVec::new();
            for (l, decl) in mir.local_decls.iter_enumerated() {
                let lty = if l.index() == mir.arg_count && sig.skip_binder().c_variadic {
                    lcx.label(decl.ty, &mut |_| None)
                } else {
                    lcx.label(decl.ty, &mut apply_initial_label)
                };

                let span = if let LocalInfo::User(
                    ClearCrossCrate::Set(
                        BindingForm::Var(var)
                    )
                ) = &decl.local_info {
                    var.pat_span
                } else {
                    DUMMY_SP
                };

                locals.push(Spanned {
                    node: lty,
                    span,
                });
            }

            functions.insert(def_id, locals);
        }

        for &def_id in opaque_func_decls.iter() {
            let sig = tcx.fn_sig(def_id);
            let mut locals: IndexVec<Local, Spanned<RefdTy<'lty, 'tcx>>> = IndexVec::new();

            if tcx.is_foreign_item(def_id) {
                assert_eq!(def_id.krate, LOCAL_CRATE);
                for (i, ty) in sig.skip_binder().inputs_and_output.iter().enumerate() {
                    let lty = if i == sig.skip_binder().inputs_and_output.len() - 1 && sig.skip_binder().c_variadic {
                        lcx.label(ty, &mut |_| None)
                    } else {
                        lcx.label(ty, &mut apply_initial_label)
                    };

                    locals.push(Spanned {
                        node: lty,
                        span: DUMMY_SP,
                    });
                }
            }
        }

        let tainted_values = constraints.solve();
        debug!("tainted values:");
        for (tainted, reason) in tainted_values {
            let place = tainted.place();
            match place.base {
                PlaceBase::Local(l) => {
                    let locals = functions
                        .get_mut(&tainted.func().expect("malformed QualifiedPlace"));
                    if tainted.func().unwrap().krate != LOCAL_CRATE {
                        continue; // does not make sense to try to taint std::{something}
                    }
                    let locals = locals.expect("QualifiedPlace referes to unknown function");
                    let base_lty = locals[l].node;
                    let modified_lty = taint_lty(
                        &lcx,
                        &tcx,
                        &mut statics,
                        place.projection,
                        base_lty,
                        None,
                    );
                    if modified_lty != base_lty {
                        locals[l].node = modified_lty;
                    }
                },
                PlaceBase::Static(ref s) => match s.kind {
                    StaticKind::Static => {
                        let base_lty = *statics.entry(s.def_id)
                            .or_insert_with(|| lcx.label(tcx.type_of(s.def_id), &mut apply_initial_label));
                        let modified_lty = taint_lty(
                            &lcx,
                            &tcx,
                            &mut statics,
                            place.projection,
                            &base_lty,
                            None
                        );
                        if modified_lty != base_lty {
                            statics.insert(s.def_id, modified_lty);
                        }
                    },
                    StaticKind::Promoted(_, _) => todo!(),
                },
            }
            debug!("  {:?}: {:?}", tainted, reason);
        }

        let functions = functions.into_iter()
            .map(|(def_id, locals)| {
                let sig = tcx.fn_sig(def_id);
                let sig_ltys = locals.raw.iter()
                    .take(sig.skip_binder().inputs_and_output.len())
                    .map(|spanned| spanned.node)
                    .collect::<Vec<_>>();

                let l_sig = FnSig {
                    inputs: lcx.mk_slice(&sig_ltys[1..]),
                    output: sig_ltys[0],
                    is_variadic: sig.skip_binder().c_variadic,
                };
                let kept_locals = locals.raw.iter()
                    .filter_map(|spanned| if spanned.span == DUMMY_SP {
                        None
                    } else {
                        Some((spanned.span, spanned.node))
                    }).collect();

                (def_id, FunctionResult {
                    sig: l_sig,
                    locals: kept_locals,
                })
            })
            .collect::<HashMap<_, _>>();

        (statics, functions)
    }
}

fn taint_lty<'lty, 'tcx>(
    lcx: &LabeledTyCtxt<'lty, Option<RefLike>>,
    tcx: &TyCtxt<'tcx>,
    statics: &mut HashMap<DefId, RefdTy<'lty, 'tcx>>,
    projection: &'tcx List<PlaceElem<'tcx>>,
    lty: RefdTy<'lty, 'tcx>,
    variant: Option<VariantIdx>,
) -> RefdTy<'lty, 'tcx> {
    let projection = projection.as_ref();
    if let Some(elem) = projection.first() {
        let remaining_projection = tcx.intern_place_elems(&projection[1..]);

        match elem {
            ProjectionElem::Deref
            | ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. } => {
                let tainted_arg = taint_lty(
                    lcx,
                    tcx,
                    statics,
                    remaining_projection,
                    lty.args[0],
                    None,
                );
                if tainted_arg == lty.args[0] {
                    lty
                } else {
                    lcx.replace_arg(lty, 0, tainted_arg)
                }
            },
            ProjectionElem::Field(f, _) => match lty.ty.kind {
                TyKind::Adt(adt, _) => {
                    let field_def = &adt
                        .variants[variant.unwrap_or(VariantIdx::from_usize(0))]
                        .fields[f.index()];

                    let field_lty = *statics.entry(field_def.did)
                        .or_insert_with(|| lcx.label(tcx.type_of(field_def.did), &mut apply_initial_label));
                    let tainted_field = taint_lty(
                        lcx,
                        tcx,
                        statics,
                        remaining_projection,
                        lcx.subst(&field_lty, &lty.args),
                        None,
                    );
                    if tainted_field != field_lty {
                        statics.insert(field_def.did, tainted_field);
                    }
                    lty
                },
                TyKind::Tuple(_) => {
                    let i = f.index();
                    let tainted_arg = taint_lty(
                        lcx,
                        tcx,
                        statics,
                        remaining_projection,
                        lty.args[i],
                        None
                    );
                    if tainted_arg == lty.args[i] {
                        lty
                    } else {
                        lcx.replace_arg(lty, i, tainted_arg)
                    }
                },
                _ => unimplemented!(),
            },
            ProjectionElem::Downcast(_, variant) => taint_lty(
                lcx,
                tcx,
                statics,
                remaining_projection,
                lty,
                Some(*variant),
            ),
            ProjectionElem::Subslice { .. } => unimplemented!(),
        }
    } else {
        if let Some(_) = lty.label {
            lcx.mk(lty.ty, lty.args, Some(false))
        } else {
            lty
        }
    }
}

fn apply_initial_label<'tcx>(ty: Ty<'tcx>) -> Option<RefLike> {
    match ty.kind {
        // TODO: does this also need TyKind::Ref?
        TyKind::RawPtr(_) => Some(true),
        TyKind::FnDef(def_id, _) => {
            debug!("nested? def {:?}", def_id);
            unimplemented!()
        },
        _ => None,
    }
}
