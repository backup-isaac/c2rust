use std::collections::HashMap;

use arena::SyncDroplessArena;
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;

use super::{FunctionResult, RefdTy};
use super::constraint::Constraints;

pub struct Ctxt<'lty, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub arena: &'lty SyncDroplessArena,
    pub constraints: Constraints<'tcx>,

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
            arena,
            constraints: Constraints::new(),
            statics: HashMap::new(),
            functions: HashMap::new(),
        }
    }
}
