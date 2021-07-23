use std::collections::HashMap;

use arena::SyncDroplessArena;
use rustc::hir::def_id::{DefId, LOCAL_CRATE};
use syntax::source_map::Span;

use crate::analysis::labeled_ty::{FnSig, LabeledTy};
use crate::analysis::ty::is_fn;
use crate::command::CommandState;
use crate::RefactorCtxt;

mod constraint;
mod context;
mod func;

use self::context::Ctxt;

pub type RefLike = bool;

/// A type where pointers are labeled as reference-like or not.
pub type RefdTy<'lty, 'tcx> = LabeledTy<'lty, 'tcx, Option<RefLike>>;
/// A signature where pointers are labeled as reference-like or not.
pub type RefdFnSig<'lty, 'tcx> = FnSig<'lty, 'tcx, Option<RefLike>>;

pub fn analyze<'lty, 'a: 'lty, 'tcx: 'a>(
    st: &CommandState,
    dcx: &RefactorCtxt<'a, 'tcx>,
    arena: &'lty SyncDroplessArena
) -> AnalysisResult<'lty, 'tcx> {
    let tcx = dcx.ty_ctxt();
    let hir_map = &dcx.hir_map();

    let funcs = tcx.mir_keys(LOCAL_CRATE).iter()
        .map(|def_id| *def_id)
        .filter(|&def_id| is_fn(hir_map, def_id) && st.marked(
            hir_map.as_local_node_id(def_id).expect("non-local def_id"),
             "target"
        )).collect();

    let mut cx = Ctxt::new(tcx, arena, funcs);
    // TODO: handle provided annotations and marks

    cx.analyze_intra();
    debug!("before propagation:");
    cx.constraints.debug_constraints();
    let (statics, functions) = cx.into_results();

    AnalysisResult {
        statics,
        functions,
        arena,
    }
}

/// The collected results of running the analysis.
pub struct AnalysisResult<'lty, 'tcx> {
    /// The ReferenceLike-labeled type of every non-fn item. This includes
    /// struct/enum fields.
    pub statics: HashMap<DefId, RefdTy<'lty, 'tcx>>,

    /// Results for each function
    pub functions: HashMap<DefId, FunctionResult<'lty, 'tcx>>,

    /// Arena used to allocate all type wrappers
    arena: &'lty SyncDroplessArena,
}

impl<'lty, 'tcx> AnalysisResult<'lty, 'tcx> {
    pub fn arena(&self) -> &'lty SyncDroplessArena {
        self.arena
    }
}

#[derive(Debug, Clone)]
pub struct FunctionResult<'lty, 'tcx: 'lty> {
    pub sig: RefdFnSig<'lty, 'tcx>,

    pub locals: HashMap<Span, RefdTy<'lty, 'tcx>>,
}

/// Print the analysis results to stderr, for debugging.
pub fn dump_results(dcx: &RefactorCtxt, results: &AnalysisResult) {
    debug!("\n === summary ===");

    let path_str = |def_id| dcx.ty_ctxt().def_path(def_id).to_string_no_crate();

    let mut ids = results.statics.keys().cloned().collect::<Vec<_>>();
    ids.sort();
    for id in ids {
        let ty = results.statics[&id];
        debug!("static {} :: {:?}", path_str(id), ty);
    }

    let mut ids = results.functions.keys().cloned().collect::<Vec<_>>();
    ids.sort();
    for id in ids {
        let fr = &results.functions[&id];
        debug!("func {} :: {:?} :: locals:", path_str(id), fr.sig);
        for (span, lty) in fr.locals.iter() {
            debug!("    {:?} :: {:?}", span, lty);
        }
    }
}
