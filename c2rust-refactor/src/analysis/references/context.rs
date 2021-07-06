use std::collections::hash_map::{Entry, HashMap};

use arena::SyncDroplessArena;
use rustc::hir::def_id::DefId;
use rustc::ty::{Ty, TyCtxt, TyKind};

use crate::analysis::labeled_ty::{FnSig, LabeledTyCtxt};

use super::{FunctionResult, RefLike, RefdTy};

pub struct Ctxt<'lty, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub lcx: LabeledTyCtxt<'lty, Option<RefLike>>,
    pub arena: &'lty SyncDroplessArena,

    pub statics: HashMap<DefId, RefdTy<'lty, 'tcx>>,
    pub functions: HashMap<DefId, FunctionResult<'lty, 'tcx>>,
}

impl<'lty, 'tcx: 'lty> Ctxt<'lty, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        arena: &'lty SyncDroplessArena
    ) -> Ctxt<'lty, 'tcx> {
        Ctxt {
            tcx,
            lcx: LabeledTyCtxt::new(&arena),
            arena,
            statics: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    pub fn static_ty(&mut self, did: DefId) -> RefdTy<'lty, 'tcx> {
        match self.statics.entry(did) {
            Entry::Vacant(e) => {
                *e.insert(self.lcx.label(self.tcx.type_of(did), &mut |ty| match ty.kind {
                    // TyKind:Ref(_, _, _) as well??
                    TyKind::RawPtr(_) => {
                        Some(true)
                    },
                    _ => None,
                }))
            }
            Entry::Occupied(e) => *e.get(),
        }
    }

    pub fn func_result(&mut self, did: DefId) -> &mut FunctionResult<'lty, 'tcx> {
        match self.functions.entry(did) {
            Entry::Vacant(e) => {
                let sig = self.tcx.fn_sig(did);

                let l_sig = {
                    let mut f = |ty: Ty<'tcx>| match ty.kind {
                        // TyKind:Ref(_, _, _) as well??
                        TyKind::RawPtr(_) => {
                            Some(true)
                        },
                        _ => None,
                    };
                    FnSig {
                        inputs: self.lcx.label_slice(sig.skip_binder().inputs(), &mut f),
                        output: self.lcx.label(sig.skip_binder().output(), &mut f),
                        is_variadic: sig.skip_binder().c_variadic,
                    }
                };

                e.insert(FunctionResult {
                    sig: l_sig,
                    locals: HashMap::new(),
                })
            }
            Entry::Occupied(e) => e.into_mut(),
        }
    }
}
