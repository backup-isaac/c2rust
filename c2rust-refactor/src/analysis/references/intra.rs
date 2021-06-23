use rustc::mir::*;

fn mark_place<'tcx>(lv: &Place<'tcx>) {
    // (*((*_1).7: *mut deflate::internal_state)).6

    if !lv.projection.is_empty() {

    }
}

fn rvalue_ref_like<'tcx>(rv: &Rvalue<'tcx>) {
    match *rv {
        Rvalue::Ref(_, BorrowKind::Mut { .. }, ref lv) => {
            println!("mark? {:?} &mut", lv);
            mark_place(lv);
        }
        Rvalue::Cast(CastKind::Misc, ref _op, _cast_raw_ty) => {
            // TODO check cast_raw_ty
            // if pointer, ref, or constant 0, mark rvalue
            // Do we need to check if types are compatible?
            println!("mark? {:?} cast", rv);
        }
        Rvalue::BinaryOp(BinOp::Offset, ref a, ref b) | Rvalue::CheckedBinaryOp(BinOp::Offset, ref a, ref b) => {
            println!("mark? {:?} offset", a);
        },
        _ => {},
    }
}

pub fn handle_basic_block<'tcx>(bbid: BasicBlock, bb: &BasicBlockData<'tcx>) {
    println!("  {:?}", bbid);

    for (_idx, s) in bb.statements.iter().enumerate() {
        if let StatementKind::Assign(box(ref lv, ref rv)) = s.kind {
            // lv: lvalue -- this is what we might have to mark as non-ref
            // rv: rvalue
            rvalue_ref_like(rv);
        }
        println!("{:?}", s);
        // match s {
        //      ptr.offset()
        //      ptr = <integer != constant 0, or sth besides pointer or ref>
        //      ptr < other_ptr <or <= >= > operator>
        //          ==> mark as non-reflike
        // }
    }

    match bb.terminator().kind {
        TerminatorKind::DropAndReplace {
            ref location,
            ref value ,
            ..
        } => {
            println!("    {:?}", location);
            println!("      {:?}", value);
        }
        TerminatorKind::Call {
            ref func,
            ref args,
            ref destination,
            ..
        } => {
            println!("    call {:?} {:?}", func, args);
        },
        _ => {},
    }
    println!("{:?}", bb.terminator());

}
