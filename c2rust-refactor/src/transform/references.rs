use arena::SyncDroplessArena;
use rustc::hir::def_id::DefId;
use syntax::ast::*;

use crate::analysis::references;
use crate::command::{CommandState, DriverCommand, Registry};
use crate::context::HirMap;
use crate::{RefactorCtxt, type_map};
use c2rust_ast_builder::IntoSymbol;

pub fn register_commands(reg: &mut Registry) {
    // TODO: references_annotate

    reg.register("references_mark_pointers", |_args| {
        Box::new(DriverCommand::new(crate::driver::Phase::Phase3, move |st, cx| {
            do_mark_pointers(st, cx);
        }))
    });
}

/// # `references_mark_pointers` Command
///
/// This is incomplete right now
///
/// Usage: `references_mark_pointers [MARK]`
///
/// Run reference analysis on functions bearing `MARK` (default: `target`),
/// then for pointer type appearing in their argument and return types,
/// apply the mark `ref` if the pointer is reference-like..
/// See `analysis/references/README.md` for details on inference.
fn do_mark_pointers(st: &CommandState, cx: &RefactorCtxt) {
    let arena = SyncDroplessArena::default();
    let ana = references::analyze(st, cx, &arena);

    // Possible opportunity to make generic / define trait
    struct AnalysisTypeSource<'lty, 'tcx: 'lty> {
        ana: references::AnalysisResult<'lty, 'tcx>,
        hir_map: HirMap<'lty, 'tcx>,
    }

    impl<'lty, 'tcx> type_map::TypeSource for AnalysisTypeSource<'lty, 'tcx> {
        type Type = references::RefdTy<'lty, 'tcx>;
        type Signature = references::RefdFnSig<'lty, 'tcx>;

        fn def_type(&mut self, did: DefId) -> Option<Self::Type> {
            self.ana.statics.get(&did).cloned()
        }

        fn fn_sig(&mut self, did: DefId) -> Option<Self::Signature> {
            self.ana.functions.get(&did).map(|f| f.sig)
        }

        fn pat_type(&mut self, p: &Pat) -> Option<Self::Type> {
            let hir_id = self.hir_map.opt_node_to_hir_id(p.id)?;
            let fn_def_id = self.hir_map.get_parent_did(hir_id);
            let f = self.ana.functions.get(&fn_def_id)?;
            f.locals.get(&p.span).map(|f| *f)

            // let mut map_fn = |opt_var: &Option<Var>| -> Option<_> {
            //     opt_var.map(|var| f.local_assign.get(var).copied()).flatten()
            // };

            // let lcx = LabeledTyCtxt::new(self.ana.arena());
            // Some(lcx.relabel(local_var, &mut map_fn))
        }
    }

    let source = AnalysisTypeSource {
        ana,
        hir_map: cx.hir_map(),
    };

    type_map::map_types(&cx.hir_map(), source, &st.krate(), |_source, ast_ty, lty| {
        if let Some(reflike) = lty.label {
            st.add_mark(ast_ty.id, (if reflike { "ref" } else { "ptr" }).into_symbol());
        }
    });
}
