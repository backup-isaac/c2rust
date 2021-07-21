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

mod constraint;
mod context;
mod func;

use self::context::Ctxt;
use self::func::FuncCtxt;

pub type RefLike = bool;

/// A type where pointers are labeled as reference-like or not.
pub type RefdTy<'lty, 'tcx> = LabeledTy<'lty, 'tcx, Option<RefLike>>;
/// A signature where pointers are labeled as reference-like or not.
pub type RefdFnSig<'lty, 'tcx> = FnSig<'lty, 'tcx, Option<RefLike>>;

fn analyze_intra<'a, 'tcx, 'lty>(
    cx: &mut Ctxt<'lty, 'tcx>,
    st: &CommandState,
    hir_map: &HirMap<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    for &def_id in tcx.mir_keys(LOCAL_CRATE).iter() {
        if !is_fn(hir_map, def_id) || !st.marked(hir_map.as_local_node_id(def_id).expect("non-local def ID"), "target") {
            continue;
        }

        // Analyze within marked functions and their deps
        // function(function definiton) {
        //     produce constraints involving local variables
        //     produce constraints involving function calls and globals
        //     call graph dependencies
        // }

        let mir = tcx.optimized_mir(def_id);
        let mut func_cx = FuncCtxt::new(cx, def_id, mir);

        for (bbid, bb) in mir.basic_blocks().iter_enumerated() {
            func_cx.analyze_basic_block(bbid, bb);
        }

        // local_cx.finish();
    }
}

pub fn analyze<'lty, 'a: 'lty, 'tcx: 'a>(
    st: &CommandState,
    dcx: &RefactorCtxt<'a, 'tcx>,
    arena: &'lty SyncDroplessArena
) -> AnalysisResult<'lty, 'tcx> {
    let mut cx = Ctxt::new(dcx.ty_ctxt(), arena);
    // TODO: handle provided annotations and marks

    analyze_intra(&mut cx, st, &dcx.hir_map(), dcx.ty_ctxt());
    cx.constraints.debug_constraints();
    cx.into()
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

impl<'lty, 'tcx> From<Ctxt<'lty, 'tcx>> for AnalysisResult<'lty, 'tcx> {
    fn from(cx: Ctxt<'lty, 'tcx>) -> AnalysisResult<'lty, 'tcx> {
        AnalysisResult {
            statics: cx.statics,
            functions: cx.functions,
            arena: cx.arena,
        }
    }
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
