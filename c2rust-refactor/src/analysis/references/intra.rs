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
    fn mark_rvalue(&mut self, rv: &Rvalue<'tcx>) -> bool {
        match *rv {
            Rvalue::Cast(CastKind::Misc, ref op, TyS { kind: TyKind::RawPtr(_), .. }) => {
                !self.can_create_reference_from_op(op)
            }
            Rvalue::BinaryOp(op, ref a, ref b) | Rvalue::CheckedBinaryOp(op, ref a, ref b) => {
                match op {
                    BinOp::Lt
                    | BinOp::Le
                    | BinOp::Ge
                    | BinOp::Gt => {
                        self.mark_operand(a);
                        self.mark_operand(b);
                    }
                    BinOp::Offset => self.mark_operand(a),
                    _ => {},
                }
                false
            },
            _ => false,
        }
    }

    /// We are looking for `{core, std}::ptr::{offset, offset_from, wrapping_offset}`
    fn names_non_reflike_function(&mut self, def_id: DefId) -> bool {
        // look for read/write unaligned?
        let def_path = self.cx.tcx.def_path(def_id);
        let crate_name = self.cx.tcx.crate_name(def_path.krate);
        if crate_name != Symbol::intern("core") && crate_name != Symbol::intern("std") {
            return false;
        }

        #[derive(Debug, Clone, Copy, PartialEq)]
        enum WantedSymbol {
            Ptr,
            Offset,
            Matched,
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
                        name == Symbol::intern("offset_from") ||
                        name == Symbol::intern("wrapping_offset") => {
                            WantedSymbol::Matched
                        }
                    _ => WantedSymbol::NotMatched
                };
                if state == WantedSymbol::NotMatched {
                    break;
                }
            }
        }

        state == WantedSymbol::Matched
    }

    pub fn handle_basic_block(&mut self, bbid: BasicBlock, bb: &BasicBlockData<'tcx>) {
        for (_idx, s) in bb.statements.iter().enumerate() {
            if let StatementKind::Assign(box(ref lv, ref rv)) = s.kind {
                let should_mark_lvalue = self.mark_rvalue(rv);
                if should_mark_lvalue {
                    self.mark_place(lv);
                }
            }
        }

        if let TerminatorKind::Call {
            ref func,
            ref args,
            ..
        } = bb.terminator().kind {
            println!("    call {:?} {:?}", func, args);
            match func {
                Operand::Copy(place) => println!("func copied {:?}", place),
                Operand::Move(place) => println!("func moved {:?}", place),
                Operand::Constant(ref c) => {
                    match c.literal.ty.kind {
                        TyKind::FnDef(did, _) => {
                            let should_mark_arg = self.names_non_reflike_function(did);
                            println!("func {} {:?}", should_mark_arg, did);
                            if should_mark_arg {
                                // TODO: should offset_from mark? if so, it should do both arguments
                                self.mark_operand(&args[0]);
                            }
                        },
                        _ => {
                            println!("func constant.kind {:?}", c.literal.ty.kind);
                            todo!();
                        }
                    }
                }
            }
        }
    }
}
