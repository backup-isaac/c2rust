use rustc::hir::def_id::DefId;
use rustc::mir::*;
use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::ty::{ConstKind, Ty, TyKind, TypeAndMut, TyS};

use c2rust_ast_builder::IntoSymbol;

use crate::analysis::references::constraint::Taint;

use super::constraint::{Constraint, QualifiedPlace};
use super::context::Ctxt;

pub struct FuncCtxt<'c, 'lty, 'a: 'lty, 'tcx: 'a> {
    cx: &'c mut Ctxt<'lty, 'tcx>,
    def_id: DefId,
    mir: &'a Body<'tcx>,
}

impl<'c, 'lty, 'a: 'lty, 'tcx: 'a> FuncCtxt<'c, 'lty, 'a, 'tcx> {
    pub fn new(
        cx: &'c mut Ctxt<'lty, 'tcx>,
        def_id: DefId,
        mir: &'a Body<'tcx>,
    ) -> FuncCtxt<'c, 'lty, 'a, 'tcx> {
        FuncCtxt {
            cx,
            def_id,
            mir,
        }
    }

    fn add_place_constraints_recursive(
        &mut self,
        from: Place<'tcx>,
        from_def_id: DefId,
        to: Place<'tcx>,
        to_def_id: DefId,
        ty: Ty<'tcx>,
    ) -> bool {
        match ty.kind {
            TyKind::Array(inner_ty, _)
            | TyKind::Slice(inner_ty) => self.add_place_constraints_recursive(
                // This local variable is bogus. This is ok since constraints
                // do not care about what is used to do the indexing
                self.cx.tcx.mk_place_index(from, Local::from_usize(0)),
                from_def_id,
                self.cx.tcx.mk_place_index(to, Local::from_usize(0)),
                to_def_id,
                inner_ty
            ),
            TyKind::RawPtr(TypeAndMut { ty, .. }) => {
                let c = Constraint {
                    from: QualifiedPlace::new(from.clone(), Some(from_def_id)),
                    to: QualifiedPlace::new(to.clone(), Some(to_def_id)),
                };
                debug!("adding {:?}", c);
                let mut added = self.cx.constraints.edges.insert(c);

                added |= self.add_place_constraints_recursive(
                    self.cx.tcx.mk_place_deref(from),
                    from_def_id,
                    self.cx.tcx.mk_place_deref(to),
                    to_def_id,
                    ty
                );

                added
            },
            TyKind::Ref(_, inner_ty, _) => self.add_place_constraints_recursive(
                self.cx.tcx.mk_place_deref(from),
                from_def_id,
                self.cx.tcx.mk_place_deref(to),
                to_def_id,
                inner_ty
            ),
            TyKind::Tuple(_) => {
                let mut added = false;
                for (i, field_ty) in ty.tuple_fields().enumerate() {
                    added |= self.add_place_constraints_recursive(
                        self.cx.tcx.mk_place_field(from.clone(), Field::from_usize(i), field_ty),
                        from_def_id,
                        self.cx.tcx.mk_place_field(to.clone(), Field::from_usize(i), field_ty),
                        to_def_id,
                        field_ty
                    );
                }
                added
            },
            _ => false,
        }
    }

    fn is_constant_zero(&self, c: &Constant<'tcx>) -> bool {
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

    fn add_place_constraints(&mut self, from: &Place<'tcx>, to: &Place<'tcx>) {
        let from_ty = from.ty(self.mir, self.cx.tcx).ty;
        if let TyKind::RawPtr(TypeAndMut { ty, .. }) = from_ty.kind {
            if self.names_c_void(ty) {
                self.add_place_constraints_recursive(
                    from.clone(),
                    self.def_id,
                    to.clone(),
                    self.def_id,
                    from_ty
                );
                return;
            }
        }

        let to_ty = to.ty(self.mir, self.cx.tcx).ty;
        self.add_place_constraints_recursive(
            from.clone(),
            self.def_id,
            to.clone(),
            self.def_id,
            to_ty
        );
    }

    fn add_operand_taint(
        &mut self,
        op: &Operand<'tcx>,
        reason: Taint<'tcx>,
        recursive: bool,
    ) {
        match op {
            Operand::Copy(place)
            | Operand::Move(place) => if recursive {
                self.cx.constraints.add_place_taint_recursive(
                    self.cx.tcx,
                    place.clone(),
                    self.def_id,
                    reason,
                    place.ty(self.mir, self.cx.tcx).ty,
                );
            } else {
                self.cx.constraints.add_place_taint(
                    place,
                    self.def_id,
                    reason,
                    place.ty(self.mir, self.cx.tcx).ty,
                )
            },
            Operand::Constant(_) => {},
        }
    }

    fn names_c_void(&self, ty: Ty<'tcx>) -> bool {
        if let TyKind::Adt(adt, _) = ty.kind {
            let def_path = self.cx.tcx.def_path(adt.did);

            if self.cx.tcx.crate_name(def_path.krate) != "core".into_symbol() {
                return false;
            }

            return def_path.data.iter().map(|it| it.data.get_opt_name()).collect::<Vec<_>>()
                == ["ffi", "c_void"].iter().map(|s| Some(s.into_symbol())).collect::<Vec<_>>();
        }
        false
    }

    fn analyze_cast(
        &mut self,
        lv: &Place<'tcx>,
        kind: CastKind,
        op: &Operand<'tcx>,
        cast_ty: Ty<'tcx>
    ) {
        assert_eq!(lv.ty(self.mir, self.cx.tcx).ty, cast_ty);
        match kind {
            CastKind::Misc => if let TyKind::RawPtr(TypeAndMut { ty: dest_base_ty, .. }) = cast_ty.kind {
                match op {
                    Operand::Copy(place)
                    | Operand::Move(place) => {
                        let place_ty = place.ty(self.mir, self.cx.tcx).ty;
                        match place_ty.kind {
                            TyKind::RawPtr(TypeAndMut { ty: pointee_ty, .. })
                            | TyKind::Ref(_, pointee_ty, _) => {
                                if TyS::same_type(pointee_ty, dest_base_ty)
                                || self.names_c_void(pointee_ty)
                                || self.names_c_void(dest_base_ty) {
                                    self.add_place_constraints(lv, place);
                                } else {
                                    self.cx.constraints.add_place_taint_recursive(
                                        self.cx.tcx,
                                        place.clone(),
                                        self.def_id,
                                        Taint::UsedInPtrCast,
                                        place_ty,
                                    );
                                }
                            }
                            _ => self.cx.constraints.add_place_taint(
                                lv,
                                self.def_id,
                                Taint::UsedInPtrCast,
                                cast_ty,
                            ),
                        }
                    },
                    Operand::Constant(c) => if !self.is_constant_zero(c) {
                        self.cx.constraints.add_place_taint(
                            lv,
                            self.def_id,
                            Taint::UsedInPtrCast,
                            cast_ty,
                        );
                    }
                }
            },
            CastKind::Pointer(_) => {
                match op {
                    Operand::Copy(place)
                    | Operand::Move(place) => {
                        self.add_place_constraints(lv, place);
                    },
                    Operand::Constant(_) => {},
                }
            }
        }
    }

    fn add_operand_constraints(&mut self, lv: &Place<'tcx>, op: &Operand<'tcx>) {
        debug!("        constraint(=) {:?} --> {:?}", lv, op);
        match op {
            Operand::Copy(place)
            | Operand::Move(place) => {
                self.add_place_constraints(lv, place);
            },
            Operand::Constant(_) => {},
        }
    }

    fn analyze_statement(&mut self, lv: &Place<'tcx>, rv: &Rvalue<'tcx>) {
        match *rv {
            Rvalue::Use(ref op) => self.add_operand_constraints(lv, op),
            Rvalue::Ref(_, _, ref op) => {
                debug!("        constraint(&) *{:?} --> {:?}", lv, op);
                self.add_place_constraints(&self.cx.tcx.mk_place_deref(lv.clone()),op);
            },
            Rvalue::Cast(kind, ref op, cast_ty) => {
                debug!("        constraint(C) {:?} --> {:?}", lv, op);
                self.analyze_cast(lv, kind, op, cast_ty);
            },
            Rvalue::BinaryOp(operator, ref a, ref b)
            | Rvalue::CheckedBinaryOp(operator, ref a, ref b) => {
                match operator {
                    BinOp::Lt
                    | BinOp::Le
                    | BinOp::Ge
                    | BinOp::Gt => {
                        debug!("        taint(<) {:?}", a);
                        debug!("        taint(<) {:?}", b);
                        self.add_operand_taint(a, Taint::UsedInArithmetic, false);
                        self.add_operand_taint(b, Taint::UsedInArithmetic, false);
                    },
                    BinOp::Offset => {
                        debug!("        taint(o) {:?}", a);
                        self.add_operand_taint(a, Taint::UsedInArithmetic, false);
                    },
                    _ => {},
                }
            },
            Rvalue::NullaryOp(ref op, ref ty) => {
                debug!("NullaryOp({:?}, {:?})", op, ty);
                unimplemented!()
            },
            Rvalue::Repeat(_, _)
            | Rvalue::Len(_)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::Discriminant(_) => {},
            Rvalue::Aggregate(ref kind, ref ops) => {
                debug!("Aggregate({:?}, {:?})", kind, ops);
                unimplemented!()
            }
        }
    }

    pub fn analyze_basic_block(
        &mut self,
        bbid: BasicBlock,
        bb: &BasicBlockData<'tcx>,
    ) -> Option<DefId> {
        debug!("  {:?}", bbid);

        for s in bb.statements.iter() {
            match s.kind {
                StatementKind::Assign(box(ref lv, ref rv)) => {
                    debug!("    {:?}", s);
                    self.analyze_statement(lv, rv);
                },
                _ => {},
            }

        }

        match bb.terminator().kind {
            TerminatorKind::DropAndReplace {
                ref location,
                ref value,
                ..
            } => self.add_operand_constraints(location, value),
            TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                ..
            } => match func {
                Operand::Constant(ref c) => {
                    let fn_def_id = match c.literal.ty.kind {
                        TyKind::FnDef(def_id, _) => def_id,
                        _ => unimplemented!(),
                    };
                    let fn_str = self.cx.tcx.def_path_str(fn_def_id);
                    debug!("    call_const {:?} = {}({:?})", destination, fn_str, args);

                    let mut depend_on_fn_analysis = false;
                    for (i, arg) in args.iter().enumerate() {
                        let callee_place = Place {
                            base: PlaceBase::Local(Local::from_usize(i + 1)),
                            projection: self.cx.tcx.intern_place_elems(&[]),
                        };
                        debug!("        constraint(a) {}::{:?} --> {:?}", fn_str, callee_place, arg);
                        depend_on_fn_analysis |= match arg {
                            Operand::Copy(place)
                            | Operand::Move(place) => self.add_place_constraints_recursive(
                                callee_place,
                                fn_def_id,
                                place.clone(),
                                self.def_id,
                                place.ty(self.mir, self.cx.tcx).ty,
                            ),
                            Operand::Constant(_) => false,
                        };
                    }

                    if depend_on_fn_analysis {
                        if self.def_id.krate == fn_def_id.krate {
                            if let Some((retval, _)) = destination {
                                let callee_place = Place {
                                    base: PlaceBase::Local(Local::from_usize(0)),
                                    projection: self.cx.tcx.intern_place_elems(&[]),
                                };
                                debug!("        constraint(r) {:?} --> {}::{:?}", retval, fn_str, callee_place);
                                self.add_place_constraints_recursive(
                                    retval.clone(),
                                    self.def_id,
                                    callee_place,
                                    fn_def_id,
                                    retval.ty(self.mir, self.cx.tcx).ty,
                                );
                            }
                        }
                        return Some(fn_def_id);
                    } else {
                        return None;
                    }
                },
                Operand::Copy(place)
                | Operand::Move(place) => {
                    for arg in args.iter() {
                        debug!("        {:?} passed to opaque {:?}", arg, place);
                        self.add_operand_taint(arg, Taint::PassedToOpaqueFnPointer(
                            QualifiedPlace::new(place.clone(), Some(self.def_id))
                        ), true);
                    }
                }
            },
            _ => {},
        }
        None
    }
}