use rustc::hir::def_id::DefId;
use rustc::mir::*;
use rustc::ty::{Ty, TyKind};
use rustc_index::vec::IndexVec;
use syntax::source_map::{DUMMY_SP, Spanned};

use super::{RefdTy, RefLike};
use super::context::Ctxt;

pub struct IntraCtxt<'c, 'lty, 'tcx: 'lty> {
    cx: &'c mut Ctxt<'lty, 'tcx>,
    def_id: DefId,
    local_tys: IndexVec<Local, Spanned<RefdTy<'lty, 'tcx>>>,
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
        }
    }

    fn label_local_ty(ty: Ty<'tcx>) -> Option<RefLike> {
        match ty.kind {
            // TODO: does this also need TyKind::Ref?
            TyKind::RawPtr(_) => {
                Some(true)
            },
            TyKind::FnDef(def_id, _) => {
                println!("nested? def {:?}", def_id);
                unimplemented!()
            },
            _ => None,
        }
    }

    pub fn finish(self) {
        println!("-- {:?} local_tys --", self.def_id);

        for (local, spanned) in self.local_tys.iter_enumerated() {
            println!("    {:?}: {:?}", local, spanned);
            let lty = spanned.node;
            if let Some(reflike) = lty.label {
                assert!(if let TyKind::RawPtr(_) = lty.ty.kind { true } else { false });
                println!("    ptr {}reflike", if reflike { "" } else { "non-" });
            }
        }

        self.cx.func_result(self.def_id).locals = self.local_tys.raw.iter().filter_map(|spanned_ity| {
            if spanned_ity.span == DUMMY_SP {
                None
            } else {
                Some((spanned_ity.span, spanned_ity.node))
            }
        }).collect();
    }

    fn mark_place(&mut self, place: &Place<'tcx>) {
        match place.base {
            PlaceBase::Local(l) => {
                // factor out to label_local_type?
                let spanned = self.local_tys[l];
                let lty = spanned.node;

                if let Some(_) = lty.label {
                    println!("mark_place b={:?} p={:?} local={:?} ty={:?}", place.base, place.projection, l, lty);
                    let relabeled = self.cx.lcx.relabel(lty, &mut |l| l.map(|_| false));
                    self.local_tys[l] = Spanned {
                        node: relabeled,
                        span: spanned.span,
                    };
                }
            },
            PlaceBase::Static(ref s) => match s.kind {
                StaticKind::Static => {
                    println!("mark_place b={:?} p={:?} static={:?}", place.base, place.projection, s);
                    let lty = self.cx.static_ty(s.def_id);
                    let relabeled = self.cx.lcx.relabel(lty, &mut |l| l.map(|_| false));
                    self.cx.statics.insert(s.def_id, relabeled);
                },
                StaticKind::Promoted(_, _) => todo!(),
            }
        }
    }

    fn mark_operand(&mut self, op: &Operand<'tcx>) {
        match *op {
            Operand::Copy(ref lv) | Operand::Move(ref lv) => self.mark_place(lv),
            Operand::Constant(_) => unimplemented!(),
        }
    }

    fn mark_lvalue(&mut self, lv: &Place<'tcx>) {
        // nop
    }

    /// Marks non-reflike operands present in `rv`. Returns true if assigning
    /// `rv` to an lvalue would make the lvalue non-reflike.
    fn mark_rvalue(&mut self, rv: &Rvalue<'tcx>) -> bool {
        match *rv {
            Rvalue::Cast(CastKind::Misc, ref _op, _cast_raw_ty) => {
                println!("mark? {:?} cast", rv);
                true // cast_raw_ty is a pointer type, op is not {pointer, ref, 0}
            }
            Rvalue::BinaryOp(op, ref a, ref b) | Rvalue::CheckedBinaryOp(op, ref a, ref b) => {
                match op {
                    BinOp::Lt
                    | BinOp::Le
                    | BinOp::Ge
                    | BinOp::Gt => {
                        println!("mark? {:?}, {:?} ineq", a, b);
                        self.mark_operand(a);
                        self.mark_operand(b);
                    }
                    BinOp::Offset => {
                        println!("mark? {:?} offset", a);
                        self.mark_operand(a);
                    },
                    _ => {},
                }
                false
            },
            _ => false,
        }
    }

    pub fn handle_basic_block(&mut self, bbid: BasicBlock, bb: &BasicBlockData<'tcx>) {
        println!("  {:?}", bbid);

        for (_idx, s) in bb.statements.iter().enumerate() {
            if let StatementKind::Assign(box(ref lv, ref rv)) = s.kind {
                // lv = Rvalue(Lt(a, b)) ==> mark a, b, lv unaffected
                // lv = Rvalue(Offset(a, n)) ==> mark a, lv unaffected
                // lv = Rvalue(Cast(x, *mut T)) ==> mark lv
                let should_mark_lvalue = self.mark_rvalue(rv);
                if should_mark_lvalue {
                    self.mark_lvalue(lv);
                }
            }
            println!("{:?}", s);
        }

        if let TerminatorKind::Call {
            ref func,
            ref args,
            ref destination,
            ..
        } = bb.terminator().kind {
            // check for calls to:
            // ptr::{offset, offset_from, wrapping_offset, wrapping_offset_from}
            println!("    call {:?} {:?}", func, args);
        }

        println!("{:?}", bb.terminator());

    }
}
