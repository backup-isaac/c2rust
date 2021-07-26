use std::collections::HashMap;
use std::iter;

use rustc::hir::Unsafety;
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use syntax::symbol::Symbol;

use c2rust_ast_builder::IntoSymbol;

/// Determines how the function specified by `def_id` should be tainted.
///
/// taints[i] == true` ==> `fn_sig(def_id).inputs_and_output[i]` should be tainted.
/// `taints.len()` may be less than `fn_sig(def_id).inputs_and_output.len()`, in
/// which case the excess elements in the function signature are not tainted.
pub fn get_function_taints<'tcx>(def_id: DefId, tcx: TyCtxt<'tcx>) -> Box<[bool]> {
    let def_path = tcx.def_path(def_id);
    let crate_name = tcx.crate_name(def_path.krate);
    let sig = tcx.fn_sig(def_id);

    // Check if it's a function we know about from core::ptr
    if crate_name == "core".into_symbol() || crate_name == "std".into_symbol() {
        let mut match_ptr = true;
        for item in def_path.data {
            if let Some(name) = item.data.get_opt_name() {
                if match_ptr {
                    match_ptr = if name == "ptr".into_symbol() {
                        false
                    } else {
                        break;
                    };
                } else {
                    return if let Some(&taints) = taint_table().get(&name) {
                        taints.into()
                    } else {
                        // We are assuming that functions in core::ptr besides those handled
                        // explicitly should taint everything
                        iter::repeat(true)
                            .take(sig.skip_binder().inputs_and_output.len())
                            .collect()
                    };
                }
            }
        }
    }

    // If we get here, the function is from outside core::ptr
    // In this case, assume a safe function taints nothing and
    // an unsafe function taints everything
    if let Unsafety::Unsafe = sig.skip_binder().unsafety {
        iter::repeat(true)
            .take(sig.skip_binder().inputs_and_output.len())
            .collect()
    } else {
        Box::new([])
    }
}

fn taint_table() -> HashMap<Symbol, &'static [bool]> {
    let mut t = HashMap::<Symbol, &'static [bool]>::new();
    t.insert("add".into_symbol(), &[true, false, true]);
    t.insert("align_offset".into_symbol(), &[]);
    t.insert("as_mut".into_symbol(), &[]);
    t.insert("as_mut_ptr".into_symbol(), &[true, true]);
    t.insert("as_ref".into_symbol(), &[]);
    t.insert("cast".into_symbol(), &[true, true]);
    t.insert("copy_from".into_symbol(), &[true, true]);
    t.insert("copy_from_nonoverlapping".into_symbol(), &[true, true]);
    t.insert("copy_to".into_symbol(), &[true, true]);
    t.insert("copy_to_nonoverlapping".into_symbol(), &[true, true]);
    t.insert("is_null".into_symbol(), &[]);
    t.insert("offset".into_symbol(), &[true, true]);
    t.insert("offset_from".into_symbol(), &[true, true]);
    t.insert("read_unaligned".into_symbol(), &[true]);
    t.insert("sub".into_symbol(), &[true, false, true]);
    t.insert("swap_nonoverlapping".into_symbol(), &[true, true]);
    t.insert("wrapping_add".into_symbol(), &[true, false, true]);
    t.insert("wrapping_offset".into_symbol(), &[true, true]);
    t.insert("wrapping_offset_from".into_symbol(), &[true, true]);
    t.insert("wrapping_sub".into_symbol(), &[true, false, true]);
    t.insert("write_bytes".into_symbol(), &[true]);
    t.insert("write_unaligned".into_symbol(), &[true]);
    t
}
