use rustc::hir::def_id::DefId;
use rustc::mir::*;
use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::ty::{ConstKind, Ty, TyKind, TyS};
use rustc_index::vec::IndexVec;
use syntax::source_map::{DUMMY_SP, Spanned};
use syntax::symbol::Symbol;

use super::{RefdTy, RefLike};
use super::context::Ctxt;

pub struct IntraCtxt<'c, 'lty, 'tcx: 'lty> {
    cx: &'c mut Ctxt<'lty, 'tcx>,
    def_id: DefId,
    local_tys: IndexVec<Local, Spanned<RefdTy<'lty, 'tcx>>>,
    no_va_arg_count: usize,
}

impl<'c, 'lty, 'a: 'lty, 'tcx: 'a> IntraCtxt<'c, 'lty, 'tcx> {
    pub fn new(
        cx: &'c mut Ctxt<'lty, 'tcx>,
        def_id: DefId,
        mir: &'a Body<'tcx>,
    ) -> IntraCtxt<'c, 'lty, 'tcx> {
        let sig = cx.func_result(def_id).sig;

        let mut local_tys = IndexVec::new();
        for (l, decl) in mir.local_decls.iter_enumerated() {
            let lty = if l.index() == 0 {
                sig.output
            } else if l.index() - 1 < mir.arg_count {
                if l.index() == mir.arg_count && sig.is_variadic {
                    cx.lcx.label(decl.ty, &mut |_| None)
                } else {
                    sig.inputs[l.index() - 1]
                }
            } else {
                cx.lcx.label(decl.ty, &mut Self::label_local_ty)
            };

            let span = if let LocalInfo::User(ClearCrossCrate::Set(BindingForm::Var(var))) = &decl.local_info {
                var.pat_span
            } else {
                DUMMY_SP
            };

            local_tys.push(Spanned {
                node: lty,
                span,
            });
        }

        IntraCtxt {
            cx,
            def_id,
            local_tys,
            no_va_arg_count: if sig.is_variadic { mir.arg_count - 1 } else { mir.arg_count },
        }
    }

    fn label_local_ty(ty: Ty<'tcx>) -> Option<RefLike> {
        match ty.kind {
            // TODO: does this also need TyKind::Ref?
            TyKind::RawPtr(_) => {
                Some(true)
            },
            TyKind::FnDef(def_id, _) => {
                debug!("nested? def {:?}", def_id);
                unimplemented!()
            },
            _ => None,
        }
    }

    pub fn finish(self) {
        debug!("-- {:?} local pointers --", self.def_id);

        for (local, spanned) in self.local_tys.iter_enumerated() {
            let lty = spanned.node;
            if let Some(_) = lty.label {
                debug!("    {:?}: {:?}", local, spanned);
            }
        }

        let inputs = self.local_tys.raw[1..=self.no_va_arg_count]
            .iter()
            .map(|s| s.node)
            .collect::<Vec<_>>();
        let inputs = self.cx.lcx.mk_slice(&inputs);

        let func = self.cx.func_result(self.def_id);

        func.sig.inputs = inputs;
        func.locals = self.local_tys.raw.iter().filter_map(|spanned_ity| {
            if spanned_ity.span == DUMMY_SP {
                None
            } else {
                Some((spanned_ity.span, spanned_ity.node))
            }
        }).collect();

        func.sig.output = self.local_tys.raw[0].node;
    }

    fn mark_place(&mut self, place: &Place<'tcx>) {
        // confirm place.projection is unimportant
        match place.base {
            PlaceBase::Local(l) => {
                let spanned = self.local_tys[l];
                let lty = spanned.node;

                if let Some(_) = lty.label {
                    let relabeled = self.cx.lcx.relabel(lty, &mut |l| l.map(|_| false));
                    self.local_tys[l] = Spanned {
                        node: relabeled,
                        span: spanned.span,
                    };
                }
            },
            PlaceBase::Static(ref s) => match s.kind {
                StaticKind::Static => {
                    let lty = self.cx.static_ty(s.def_id);
                    let relabeled = self.cx.lcx.relabel(lty, &mut |l| l.map(|_| false));
                    self.cx.statics.insert(s.def_id, relabeled);
                },
                StaticKind::Promoted(_, _) => todo!(),
            }
        }
    }

    fn is_reflike(&mut self, place: &Place<'tcx>) -> bool {
        let lty = match place.base {
            PlaceBase::Local(l) => self.local_tys[l].node,
            PlaceBase::Static(ref s) => match s.kind {
                StaticKind::Static => self.cx.static_ty(s.def_id),
                StaticKind::Promoted(_, _) => todo!(),
            }
        };

        lty.label.unwrap_or(true)
    }

    fn mark_operand(&mut self, op: &Operand<'tcx>) {
        match *op {
            Operand::Copy(ref lv) | Operand::Move(ref lv) => self.mark_place(lv),
            Operand::Constant(_) => unimplemented!(),
        }
    }

    fn can_create_reference_from_ty(&mut self, ty: Ty<'tcx>) -> bool {
        match ty.kind {
            TyKind::RawPtr(_) | TyKind::Ref(_, _, _) => true,
            // should other types like slices or fn pointers return true?
            _ => false,
        }
    }

    fn can_create_reference_from_op(&mut self, op: &Operand<'tcx>) -> bool {
        match *op {
            Operand::Copy(ref lv) | Operand::Move(ref lv) => {
                match lv.base {
                    PlaceBase::Local(l) => {
                        let ty = self.local_tys[l].node.ty;
                        self.can_create_reference_from_ty(ty)
                    }
                    PlaceBase::Static(ref s) => match s.kind {
                        StaticKind::Static => {
                            let ty = self.cx.static_ty(s.def_id).ty;
                            self.can_create_reference_from_ty(ty)
                        },
                        StaticKind::Promoted(_, _) => todo!(),
                    }
                }
            }
            Operand::Constant(ref c) => {
                (match c.literal.ty.kind {
                    TyKind::Int(_) | TyKind::Uint(_) => true,
                    _ => false,
                }) && (match c.literal.val {
                    // e.g. "0 as usize" for creating a null pointer
                    // check for Scalar::Ptr?
                    ConstKind::Value(ConstValue::Scalar(Scalar::Raw { data, .. })) => data == 0,
                    _ => false,
                })
            }
        }
    }

    /// Marks non-reflike operands present in `rv`. Returns true if assigning
    /// `rv` to an lvalue would make the lvalue non-reflike.
    fn mark_rvalue(&mut self, rv: &Rvalue<'tcx>, propagate_backward: RefLike) -> bool {
        match *rv {
            Rvalue::Use(ref a) if !propagate_backward => {
                // For x = a where x is non-reflike, a needs to be marked as well.
                debug!("          ^---- mark({:?}, propagated)", a);
                self.mark_operand(a);
                false
            }
            Rvalue::Cast(CastKind::Misc, ref op, TyS { kind: TyKind::RawPtr(_), .. }) => {
                !self.can_create_reference_from_op(op)
            }
            Rvalue::BinaryOp(op, ref a, ref b) | Rvalue::CheckedBinaryOp(op, ref a, ref b) => {
                match op {
                    BinOp::Lt
                    | BinOp::Le
                    | BinOp::Ge
                    | BinOp::Gt => {
                        debug!("          ^---- mark({:?}, compar)", a);
                        debug!("          ^---- mark({:?}, compar)", b);
                        self.mark_operand(a);
                        self.mark_operand(b);
                    }
                    BinOp::Offset => {
                        debug!("          ^---- mark({:?}, offset)", a);
                        self.mark_operand(a);
                    },
                    _ => {},
                }
                false
            },
            _ => false,
        }
    }

    /// We are looking for `{core, std}::ptr::{offset, offset_from, wrapping_offset}`
    fn mark_non_reflike_fn_args(&mut self, def_id: DefId, args: &[Operand<'tcx>]) {
        // look for read/write unaligned?
        let def_path = self.cx.tcx.def_path(def_id);
        let crate_name = self.cx.tcx.crate_name(def_path.krate);
        if crate_name != Symbol::intern("core") && crate_name != Symbol::intern("std") {
            return;
        }

        #[derive(Debug, Clone, Copy, PartialEq)]
        enum WantedSymbol {
            Ptr,
            Offset,
            MarkFirstArg,
            MarkTwoArgs,
            NotMatched
        }
        let mut state = WantedSymbol::Ptr;

        for item in def_path.data {
            if let Some(name) = item.data.get_opt_name() {
                state = match state {
                    WantedSymbol::Ptr if name == Symbol::intern("ptr") => {
                        WantedSymbol::Offset
                    }
                    WantedSymbol::Offset if
                        name == Symbol::intern("offset") ||
                        name == Symbol::intern("wrapping_offset") => {
                            WantedSymbol::MarkFirstArg
                        }
                    WantedSymbol::Offset if name == Symbol::intern("offset_from") => {
                        WantedSymbol::MarkTwoArgs
                    }
                    _ => WantedSymbol::NotMatched
                };
                if state == WantedSymbol::NotMatched {
                    break;
                }
            }
        }

        match state {
            WantedSymbol::MarkFirstArg => {
                debug!("          ^---- mark({:?}, call)", &args[0]);
                self.mark_operand(&args[0]);
            }
            WantedSymbol::MarkTwoArgs => {
                debug!("          ^---- mark({:?}, call)", &args[0]);
                debug!("          ^---- mark({:?}, call)", &args[1]);
                self.mark_operand(&args[0]);
                self.mark_operand(&args[1]);
            }
            _ => {}
        }
    }

    pub fn handle_basic_block(&mut self, bbid: BasicBlock, bb: &BasicBlockData<'tcx>) {
        debug!("  {:?}", bbid);

        // With interprocedural analysis, this hardcoding can be removed
        if let TerminatorKind::Call {
            ref func,
            ref args,
            ..
        } = bb.terminator().kind {
            debug!("    call {:?} {:?}", func, args);
            match func {
                Operand::Copy(place) => debug!("func copied {:?}", place),
                Operand::Move(place) => debug!("func moved {:?}", place),
                Operand::Constant(ref c) => {
                    match c.literal.ty.kind {
                        TyKind::FnDef(did, _) => self.mark_non_reflike_fn_args(did, args),
                        _ => {
                            debug!("func constant.kind {:?}", c.literal.ty.kind);
                            todo!();
                        }
                    }
                }
            }
        }

        for s in bb.statements.iter().rev() {
            if let StatementKind::Assign(box(ref lv, ref rv)) = s.kind {
                debug!("    {:?}", s);

                let propagate = self.is_reflike(lv);
                let should_mark_lvalue = self.mark_rvalue(rv, propagate);
                if should_mark_lvalue {
                    self.mark_place(lv);
                    debug!("      ^---- mark({:?}, =cast)", lv);
                }
            }
        }
    }
}
