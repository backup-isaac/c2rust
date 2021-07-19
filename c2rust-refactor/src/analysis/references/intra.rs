use rustc::hir::def_id::DefId;
use rustc::mir::*;
use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::ty::{ConstKind, List, Ty, TyKind, TypeAndMut, TyS};
use rustc_index::vec::IndexVec;
use rustc_target::abi::VariantIdx;
use syntax::source_map::{DUMMY_SP, Spanned};

use c2rust_ast_builder::IntoSymbol;

use super::{RefdTy, RefLike};
use super::context::Ctxt;

pub struct IntraCtxt<'c, 'lty, 'a: 'lty, 'tcx: 'a> {
    cx: &'c mut Ctxt<'lty, 'tcx>,
    def_id: DefId,
    local_tys: IndexVec<Local, Spanned<RefdTy<'lty, 'tcx>>>,
    mir: &'a Body<'tcx>,
    no_va_arg_count: usize,
}

impl<'c, 'lty, 'a: 'lty, 'tcx: 'a> IntraCtxt<'c, 'lty, 'a, 'tcx> {
    pub fn new(
        cx: &'c mut Ctxt<'lty, 'tcx>,
        def_id: DefId,
        mir: &'a Body<'tcx>,
    ) -> IntraCtxt<'c, 'lty, 'a, 'tcx> {
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
            mir,
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

    fn recurse_on_arg(
        &mut self,
        remaining_projection: &'tcx List<PlaceElem<'tcx>>,
        lty: RefdTy<'lty, 'tcx>,
        arg_index: usize
    ) -> RefdTy<'lty, 'tcx> {
        let marked_arg = self.mark_ltys(remaining_projection, lty.args[arg_index], None);
        if marked_arg == lty.args[arg_index] {
            lty
        } else {
            self.cx.lcx.replace_arg(lty, arg_index, marked_arg)
        }
    }

    /// Recursively projects through `lty`'s type tree to mark the innermost type as
    /// "non-reflike"; for instance, a projection accessing a struct field should cause the
    /// field to be marked as opposed to a pointer to the struct.
    /// Returns a new, modified lty
    fn mark_ltys(
        &mut self,
        projection: &'tcx List<PlaceElem<'tcx>>,
        lty: RefdTy<'lty, 'tcx>,
        variant: Option<VariantIdx>,
    ) -> RefdTy<'lty, 'tcx> {
        let projection = projection.as_ref();
        if let Some(elem) = projection.first() {
            let remaining_projection = self.cx.tcx.intern_place_elems(&projection[1..]);

            match elem {
                ProjectionElem::Deref
                | ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. } => self.recurse_on_arg(remaining_projection, lty, 0),
                ProjectionElem::Field(f, _) => match lty.ty.kind {
                    TyKind::Adt(adt, _) => {
                        let field_def = &adt
                            .variants[variant.unwrap_or(VariantIdx::from_usize(0))]
                            .fields[f.index()];
                        let field_lty = self.cx.static_ty(field_def.did);
                        let marked_field = self.mark_ltys(remaining_projection, self.cx.lcx.subst(field_lty, &lty.args), None);

                        // Mark the field, not a pointer to the containing type
                        if marked_field != field_lty {
                            debug!("static {:?} :: {:?} ==> {:?}", field_def.did, self.cx.statics.get(&field_def.did), marked_field);
                            self.cx.statics.insert(field_def.did, marked_field);
                        }
                        lty
                    }
                    TyKind::Tuple(_) => self.recurse_on_arg(remaining_projection, lty, f.index()),
                    _ => unimplemented!(),
                },
                ProjectionElem::Downcast(_, variant) => self.mark_ltys(remaining_projection, lty, Some(*variant)),
                ProjectionElem::Subslice { .. } => unimplemented!(),
            }
        } else {
            if let Some(true) = lty.label {
                self.cx.lcx.mk(lty.ty, lty.args, Some(false))
            } else {
                lty
            }
        }
    }

    fn project_lty(
        &mut self,
        lty: RefdTy<'lty, 'tcx>,
        projection: &'tcx List<PlaceElem<'tcx>>,
        variant: Option<VariantIdx>,
    ) -> RefdTy<'lty, 'tcx> {
        let projection = projection.as_ref();
        if let Some(elem) = projection.first() {
            let remaining_projection = self.cx.tcx.intern_place_elems(&projection[1..]);

            match elem {
                ProjectionElem::Deref
                | ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. } => self.project_lty(lty.args[0], remaining_projection, None),
                ProjectionElem::Field(f, _) => match lty.ty.kind {
                    TyKind::Adt(adt, _) => {
                        let field_def = &adt
                            .variants[variant.unwrap_or(VariantIdx::from_usize(0))]
                            .fields[f.index()];
                        let field_lty = self.cx.static_ty(field_def.did);
                        self.project_lty(self.cx.lcx.subst(field_lty, &lty.args), remaining_projection, None)
                    }
                    TyKind::Tuple(_) => self.project_lty(lty.args[f.index()], remaining_projection, None),
                    _ => lty,
                }
                ProjectionElem::Downcast(_, variant) => self.project_lty(lty, remaining_projection, Some(*variant)),
                ProjectionElem::Subslice { .. } => unimplemented!(),
            }
        } else {
            lty
        }
    }

    fn get_projected_place_lty(&mut self, place: &Place<'tcx>) -> RefdTy<'lty, 'tcx> {
        let lty = self.get_place_lty(&place.base);
        self.project_lty(lty, place.projection, None)
    }

    fn get_place_lty(&mut self, pb: &PlaceBase) -> RefdTy<'lty, 'tcx> {
        match *pb {
            PlaceBase::Local(l) => self.local_tys[l].node,
            PlaceBase::Static(ref s) => match s.kind {
                StaticKind::Static => self.cx.static_ty(s.def_id),
                StaticKind::Promoted(_, _) => todo!(),
            }
        }
    }

    fn try_set_through_projection(
        &mut self,
        to_project: RefdTy<'lty, 'tcx>,
        projection: &'tcx List<PlaceElem<'tcx>>,
        lty: RefdTy<'lty, 'tcx>,
        variant: Option<VariantIdx>
    ) -> Option<RefdTy<'lty, 'tcx>> {
        let projection = projection.as_ref();
        if let Some(elem) = projection.first() {
            let remaining_projection = self.cx.tcx.intern_place_elems(&projection[1..]);

            match elem {
                ProjectionElem::Deref
                | ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. } => {
                    let ret = self.try_set_through_projection(to_project.args[0], remaining_projection, lty, None);

                    ret.map(|returned_lty| {
                        if to_project.args[0].ty == lty.ty {
                            self.cx.lcx.replace_arg(to_project, 0, returned_lty)
                        } else {
                            returned_lty
                        }
                    })
                },
                ProjectionElem::Field(f, _) => match to_project.ty.kind {
                    TyKind::Adt(adt, _) => {
                        let field_def = &adt
                            .variants[variant.unwrap_or(VariantIdx::from_usize(0))]
                            .fields[f.index()];
                        let field_lty = self.cx.static_ty(field_def.did);
                        let ret = self.try_set_through_projection(field_lty, remaining_projection, lty, None);
                        if let Some(returned_lty) = ret {
                            debug!("static {:?} :: {:?} ==> {:?}", field_def.did, self.cx.statics.get(&field_def.did), returned_lty);
                            assert_eq!(self.cx.statics.get(&field_def.did).unwrap().ty, returned_lty.ty);
                            self.cx.statics.insert(field_def.did, returned_lty);
                        }
                        None
                    }
                    TyKind::Tuple(_) => {
                        let ret = self.try_set_through_projection(to_project.args[f.index()], remaining_projection, lty, None);

                        ret.map(|returned_lty| {
                            if to_project.args[f.index()].ty == lty.ty {
                                self.cx.lcx.replace_arg(to_project, f.index(), returned_lty)
                            } else {
                                returned_lty
                            }
                        })
                    }
                    _ => unimplemented!(),
                }
                ProjectionElem::Downcast(_, variant) => self.try_set_through_projection(to_project, remaining_projection, lty, Some(*variant)),
                ProjectionElem::Subslice { .. } => unimplemented!(),
            }
        } else {
            Some(lty)
        }
    }

    fn set_projected_place_lty(&mut self, place: &Place<'tcx>, lty: RefdTy<'lty, 'tcx>) {
        let to_project = self.get_place_lty(&place.base);
        let ret = self.try_set_through_projection(to_project, place.projection, lty, None);
        if let Some(returned_lty) = ret {
            self.set_place_lty(&place.base, returned_lty);
        }
    }

    fn set_place_lty(&mut self, pb: &PlaceBase, lty: RefdTy<'lty, 'tcx>) {
        match *pb {
            PlaceBase::Local(l) => {
                let span = self.local_tys[l].span;
                debug!("local {:?} :: {:?} ==> {:?}", l, self.local_tys[l].node, lty);
                assert_eq!(self.local_tys[l].node.ty, lty.ty);
                self.local_tys[l] = Spanned {
                    node: lty,
                    span
                };
            },
            PlaceBase::Static(ref s) => match s.kind {
                StaticKind::Static => {
                    debug!("static {:?} :: {:?} ==> {:?}", s.def_id, self.cx.statics.get(&s.def_id), lty);
                    self.cx.statics.insert(s.def_id, lty);
                },
                StaticKind::Promoted(_, _) => todo!(),
            },
        }
    }

    fn mark_place(&mut self, place: &Place<'tcx>) {
        match place.ty(self.mir, self.cx.tcx).ty.kind {
            TyKind::RawPtr(_) => {},
            _ => return, // not useful to mark anything else
        }

        let base_lty = self.get_place_lty(&place.base);
        let modified_lty = self.mark_ltys(place.projection, base_lty, None);

        if modified_lty != base_lty {
            self.set_place_lty(&place.base, modified_lty);
        }
    }

    fn contains_non_reflike(&self, lty: RefdTy<'lty, 'tcx>) -> bool {
        if let Some(false) = lty.label {
            true
        } else {
            for arg in lty.args {
                if self.contains_non_reflike(arg) {
                    return true;
                }
            }
            false
        }
    }

    fn mark_operand(&mut self, op: &Operand<'tcx>) {
        match *op {
            Operand::Copy(ref lv) | Operand::Move(ref lv) => self.mark_place(lv),
            Operand::Constant(_) => {},
        }
    }

    fn can_create_reference_from_ty(&mut self, ty: Ty<'tcx>, dest_base_type: Ty<'tcx>) -> bool {
        match ty.kind {
            TyKind::RawPtr(TypeAndMut { ty: pointee_ty, .. })
            | TyKind::Ref(_, pointee_ty, _) => TyS::same_type(pointee_ty, dest_base_type),
            // should other types like slices or fn pointers return true?
            _ => false,
        }
    }

    fn can_create_reference_from_op(&mut self, op: &Operand<'tcx>, dest_base_type: Ty<'tcx>) -> bool {
        match *op {
            Operand::Copy(ref lv) | Operand::Move(ref lv) => {
                let lty = self.get_projected_place_lty(lv).ty;
                let can_create = self.can_create_reference_from_ty(lty, dest_base_type);
                if !can_create {
                    // If e.g. we cast a pointer of type A to type B, neither can become a reference
                    // This ensures the operand being casted is marked accordingly
                    debug!("          ^---- mark({:?}, cast)", lv);
                    self.mark_place(lv);
                }
                can_create
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
    fn mark_rvalue(&mut self, rv: &Rvalue<'tcx>, propagate_backward: RefdTy<'lty, 'tcx>) -> bool {
        match *rv {
            Rvalue::Use(ref a) if self.contains_non_reflike(propagate_backward) => {
                // For x = a where x is non-reflike, a needs to be marked as well.
                debug!("          ^---- mark({:?}, propagated)", a);
                match *a {
                    Operand::Copy(ref place)
                    | Operand::Move(ref place) => {
                        assert_eq!(propagate_backward.ty, a.ty(self.mir, self.cx.tcx));
                        self.set_projected_place_lty(place, propagate_backward);
                    },
                    Operand::Constant(_) => {}
                }
                false
            }
            Rvalue::Ref(_, ref kind, ref place) => {
                debug!("&{:?} of {:?}: {:?}", kind, place, place.ty(self.mir, self.cx.tcx).ty);
                false
            }
            Rvalue::Cast(CastKind::Misc, ref op, TyS { kind: TyKind::RawPtr(TypeAndMut { ty, .. }), .. }) => {
                debug!("cast to *{:?}", ty);
                !self.can_create_reference_from_op(op, ty)
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
        if crate_name != "core".into_symbol() && crate_name != "std".into_symbol() {
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
                    WantedSymbol::Ptr if name == "ptr".into_symbol() => {
                        WantedSymbol::Offset
                    }
                    WantedSymbol::Offset if
                        name == "offset".into_symbol() ||
                        name == "wrapping_offset".into_symbol() => {
                            WantedSymbol::MarkFirstArg
                        }
                    WantedSymbol::Offset if
                        name == "offset_from".into_symbol() ||
                        name == "wrapping_offset_from".into_symbol() => {
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
            ref destination,
            ..
        } = bb.terminator().kind {
            debug!("    call {:?}({:?}) -> {:?}", func, args, destination);
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

                let lvalue_lty = self.get_projected_place_lty(lv);
                let should_mark_lvalue = self.mark_rvalue(rv, lvalue_lty);
                if should_mark_lvalue {
                    self.mark_place(lv);
                    debug!("      ^---- mark({:?}, =cast)", lv);
                }
            }
        }
    }
}
