use syntax::ast::*;
use syntax::visit::{self, Visitor};

pub fn meta_item_list(meta: &MetaItem) -> Result<&[NestedMetaItem], &'static str> {
    match meta.kind {
        MetaItemKind::List(ref xs) => Ok(xs),
        _ => Err("expected MetaItemKind::List"),
    }
}

pub struct AttrVisitor<'ast> {
    pub def_attrs: Vec<(NodeId, &'ast [Attribute])>,
}

impl<'ast> Visitor<'ast> for AttrVisitor<'ast> {
    fn visit_item(&mut self, i: &'ast Item) {
        match i.kind {
            ItemKind::Fn(..) | ItemKind::Static(..) | ItemKind::Const(..) => {
                if !i.attrs.is_empty() {
                    self.def_attrs.push((i.id, &i.attrs));
                }
            }
            _ => {}
        }

        visit::walk_item(self, i);
    }

    fn visit_impl_item(&mut self, i: &'ast ImplItem) {
        match i.kind {
            ImplItemKind::Method(..) | ImplItemKind::Const(..) => {
                if !i.attrs.is_empty() {
                    self.def_attrs.push((i.id, &i.attrs));
                }
            }
            _ => {}
        }

        visit::walk_impl_item(self, i);
    }

    fn visit_foreign_item(&mut self, i: &'ast ForeignItem) {
        match i.kind {
            // TODO: Foreign statics?
            ForeignItemKind::Fn(..) => {
                if !i.attrs.is_empty() {
                    self.def_attrs.push((i.id, &i.attrs));
                }
            }
            _ => {}
        }

        visit::walk_foreign_item(self, i);
    }

    fn visit_struct_field(&mut self, sf: &'ast StructField) {
        if !sf.attrs.is_empty() {
            self.def_attrs.push((sf.id, &sf.attrs));
        }

        visit::walk_struct_field(self, sf);
    }
}
