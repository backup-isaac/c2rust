
use std::collections::HashMap;

use arena::SyncDroplessArena;
use rustc::hir::def_id::{DefId, LOCAL_CRATE};
use rustc::ty::TyCtxt;
use syntax::source_map::Span;

use crate::analysis::labeled_ty::{FnSig, LabeledTy};
use crate::analysis::ty::is_fn;
use crate::command::CommandState;
use crate::context::HirMap;
use crate::RefactorCtxt;

mod intra;

pub type RefLike = bool;

/// A type where pointers are labeled as reference-like or not.
pub type RefdTy<'lty, 'tcx> = LabeledTy<'lty, 'tcx, Option<RefLike>>;
/// A signature where pointers are labeled as reference-like or not.
pub type RefdFnSig<'lty, 'tcx> = FnSig<'lty, 'tcx, Option<RefLike>>;

fn analyze_intra<'a, 'tcx, 'lty>(
    // _cx: &mut Ctxt<'lty, 'tcx>,
    hir_map: &HirMap<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    for &def_id in tcx.mir_keys(LOCAL_CRATE).iter() {
        if !is_fn(hir_map, def_id) {
            continue;
        }

        let mir = tcx.optimized_mir(def_id);

        // another layer of context?
        for (bbid, bb) in mir.basic_blocks().iter_enumerated() {
            intra::handle_basic_block(bbid, bb);
        }
    }
}

pub fn analyze<'lty, 'a: 'lty, 'tcx: 'a>(
    _st: &CommandState,
    dcx: &RefactorCtxt<'a, 'tcx>,
    arena: &'lty SyncDroplessArena
) -> AnalysisResult<'lty, 'tcx> {
    // TODO: handle provided annotations and marks

    // This analysis is entirely local. Unsure if attempting to
    // analyze across functions is even useful here
    analyze_intra(/*&mut dcx,*/ &dcx.hir_map(), dcx.ty_ctxt());
    AnalysisResult {
        statics: HashMap::new(),
        functions: HashMap::new(),
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
pub fn dump_results(_dcx: &RefactorCtxt, _results: &AnalysisResult) {
    eprintln!("references dump_results");
}
