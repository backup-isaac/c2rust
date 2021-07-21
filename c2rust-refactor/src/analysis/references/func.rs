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
        to: Place<'tcx>,
        ty: Ty<'tcx>,
    ) {
        debug!("type {:?}", ty);
        match ty.kind {
            TyKind::Array(inner_ty, _)
            | TyKind::Slice(inner_ty) => self.add_place_constraints_recursive(
                // This local variable is bogus. This is ok since constraints
                // do not care about what is used to do the indexing
                self.cx.tcx.mk_place_index(from, Local::from_usize(0)),
                self.cx.tcx.mk_place_index(to, Local::from_usize(0)),
                inner_ty
            ),
            TyKind::RawPtr(TypeAndMut { ty, .. }) => {
                let c = Constraint {
                    from: QualifiedPlace::new(from.clone(), Some(self.def_id)),
                    to: QualifiedPlace::new(to.clone(), Some(self.def_id)),
                };
                debug!("adding {:?}", c);
                self.cx.constraints.edges.insert(c);

                self.add_place_constraints_recursive(
                    self.cx.tcx.mk_place_deref(from),
                    self.cx.tcx.mk_place_deref(to),
                    ty
                );
            },
            TyKind::Ref(_, inner_ty, _) => self.add_place_constraints_recursive(
                self.cx.tcx.mk_place_deref(from),
                self.cx.tcx.mk_place_deref(to),
                inner_ty
            ),
            TyKind::Tuple(_) => {
                for (i, field_ty) in ty.tuple_fields().enumerate() {
                    self.add_place_constraints_recursive(
                        self.cx.tcx.mk_place_field(from.clone(), Field::from_usize(i), field_ty),
                        self.cx.tcx.mk_place_field(to.clone(), Field::from_usize(i), field_ty),
                        field_ty
                    );
                }
            },
            _ => {},
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
                self.add_place_constraints_recursive(from.clone(), to.clone(), from_ty);
                return;
            }
        }

        let to_ty = to.ty(self.mir, self.cx.tcx).ty;
        self.add_place_constraints_recursive(from.clone(), to.clone(), to_ty);
    }

    fn names_c_void(&self, ty: Ty<'tcx>) -> bool {
        if let TyKind::Adt(adt, _) = ty.kind {
            let def_path = self.cx.tcx.def_path(adt.did);
            if let Some(name) = def_path.data.last().expect("empty def path").data.get_opt_name() {
                if name == "c_void".into_symbol() {
                    debug!(
                        "c_void crate {:?} def_path {:?}",
                        self.cx.tcx.crate_name(def_path.krate),
                        self.cx.tcx.def_path_str(adt.did),
                    );
                    return true;
                }
            }
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
        match kind {
            CastKind::Misc => if let TyKind::RawPtr(TypeAndMut { ty: dest_base_ty, .. }) = cast_ty.kind {
                match op {
                    Operand::Copy(place)
                    | Operand::Move(place) => match place.ty(self.mir, self.cx.tcx).ty.kind {
                        TyKind::RawPtr(TypeAndMut { ty: pointee_ty, .. })
                        | TyKind::Ref(_, pointee_ty, _) => {
                            // TODO: check for void *
                            if TyS::same_type(pointee_ty, dest_base_ty)
                            || self.names_c_void(pointee_ty)
                            || self.names_c_void(dest_base_ty) {
                                self.add_place_constraints(lv, place);
                            } else {
                                self.cx.constraints.add_taint(
                                    QualifiedPlace::new(place.clone(), Some(self.def_id)),
                                    Taint::UsedInPtrCast
                                );
                            }
                        }
                        _ => self.cx.constraints.add_taint(
                            QualifiedPlace::new(place.clone(), Some(self.def_id)),
                            Taint::UsedInPtrCast
                        ),
                    },
                    Operand::Constant(c) => if !self.is_constant_zero(c) {
                        self.cx.constraints.add_taint(
                            QualifiedPlace::new(lv.clone(), Some(self.def_id)),
                            Taint::UsedInPtrCast
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

    fn analyze_statement(&mut self, lv: &Place<'tcx>, rv: &Rvalue<'tcx>) {
        match *rv {
            Rvalue::Use(ref op) => {
                debug!("        constraint(=) {:?} --> {:?}", lv, op);
                match op {
                    Operand::Copy(place)
                    | Operand::Move(place) => {
                        self.add_place_constraints(lv, place);
                    },
                    Operand::Constant(_) => {},
                }
            },
            Rvalue::Ref(_, _, ref op) => {
                debug!("        constraint(&) *{:?} --> {:?}", lv, op);
                self.add_place_constraints(&self.cx.tcx.mk_place_deref(lv.clone()), op);
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
                    },
                    BinOp::Offset => {
                        debug!("        taint(o) {:?}", a);
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

    // TODO: encapsulate this elsewhere?
    pub fn analyze_basic_block(&mut self, bbid: BasicBlock, bb: &BasicBlockData<'tcx>) {
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
            } => {
                debug!("    {:?} <=d/r= {:?}", location, value);
            },
            TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                ..
            } => {
                debug!("    {:?} = {:?}({:?})", destination, func, args);
            },
            _ => {},
        }
    }
}