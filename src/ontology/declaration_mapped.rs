//! An index that provides rapid look up via declaration kind

use crate::model::{
    AnnotatedComponent, Component, ComponentKind, ForIRI, IRI, Kinded, NamedEntityKind,
    NamedOWLEntityKind, RcAnnotatedComponent, RcStr,
};

use super::indexed::ForIndex;
use super::indexed::OntologyIndex;

use std::collections::HashMap;
use std::collections::HashSet;
use std::marker::PhantomData;

#[derive(Debug)]
pub struct DeclarationMappedIndex<A, AA> {
    // Map between IRIs and their kinds
    kinds: HashMap<IRI<A>, NamedEntityKind>,
    // Every kind each IRI is declared as; more than one for a punned IRI
    declared: HashMap<IRI<A>, Vec<NamedEntityKind>>,
    // Set of punned IRIs
    puns: HashSet<IRI<A>>,
    pd: PhantomData<AA>,
}

impl<A: ForIRI, AA: ForIndex<A>> DeclarationMappedIndex<A, AA> {
    pub fn new() -> DeclarationMappedIndex<A, AA> {
        DeclarationMappedIndex::default()
    }

    pub fn is_annotation_property(&self, iri: &IRI<A>) -> bool {
        matches! {
            self.declaration_kind(iri),
            Some(NamedOWLEntityKind::AnnotationProperty)
        }
    }

    pub fn is_declaration_kind(&self, iri: &IRI<A>, kind: NamedOWLEntityKind) -> bool {
        self.declaration_kind(iri).is_some_and(|k| k == kind)
    }

    pub fn declaration_kind(&self, iri: &IRI<A>) -> Option<NamedOWLEntityKind> {
        self.kind(iri).and_then(|e| e.as_owl())
    }

    pub fn declaration_kind_prefer_punned_individual(
        &self,
        iri: &IRI<A>,
    ) -> Option<NamedOWLEntityKind> {
        self.kind_prefer_punned_individual(iri)
            .and_then(|e| e.as_owl())
    }

    /// Whether `iri` is declared as `kind`, also when it is punned and
    /// [`declaration_kind`](Self::declaration_kind) gives another kind.
    pub fn is_declared_as(&self, iri: &IRI<A>, kind: NamedOWLEntityKind) -> bool {
        self.declared
            .get(iri)
            .is_some_and(|kinds| kinds.iter().any(|k| k.as_owl() == Some(kind)))
            || self.declaration_kind(iri) == Some(kind)
    }

    /// The first of `preferred` that `iri` is declared as, otherwise
    /// its [`declaration_kind`](Self::declaration_kind).
    ///
    /// A punned IRI has several kinds, of which `declaration_kind`
    /// gives one; which one depends on the order of the
    /// declarations. Where the position of the IRI tells which kinds
    /// can stand there (a property in a restriction, a class in a
    /// class axiom), this gives the right one in either order.
    pub fn declaration_kind_preferring(
        &self,
        iri: &IRI<A>,
        preferred: &[NamedOWLEntityKind],
    ) -> Option<NamedOWLEntityKind> {
        preferred
            .iter()
            .copied()
            .find(|kind| self.is_declared_as(iri, *kind))
            .or_else(|| self.declaration_kind(iri))
    }

    pub fn is_kind(&self, iri: &IRI<A>, kind: NamedEntityKind) -> bool {
        self.kind(iri).is_some_and(|k| k == kind)
    }

    pub fn kind(&self, iri: &IRI<A>) -> Option<NamedEntityKind> {
        self.kinds
            .get(iri)
            .cloned()
            // If the IRI is to a built in property (such as Thing) it
            // won't have been declared but should return the right
            // thing.
            .or_else(|| crate::vocab::to_built_in_entity(iri).map(|e| e.into()))
    }

    pub fn kind_prefer_punned_individual(&self, iri: &IRI<A>) -> Option<NamedEntityKind> {
        if self.puns.contains(iri) {
            Some(NamedEntityKind::NamedIndividual)
        } else {
            self.kind(iri)
        }
    }

    pub fn puns(&self) -> &HashSet<IRI<A>> {
        &self.puns
    }

    fn aa_to_ne(&self, ax: &AnnotatedComponent<A>) -> Option<NamedEntityKind> {
        match ax.kind() {
            ComponentKind::DeclareClass
            | ComponentKind::DeclareObjectProperty
            | ComponentKind::DeclareAnnotationProperty
            | ComponentKind::DeclareDataProperty
            | ComponentKind::DeclareDatatype
            | ComponentKind::DeclareNamedIndividual => match &ax.component {
                Component::DeclareClass(_) => Some(NamedEntityKind::Class),
                Component::DeclareObjectProperty(_) => Some(NamedEntityKind::ObjectProperty),
                Component::DeclareAnnotationProperty(_) => {
                    Some(NamedEntityKind::AnnotationProperty)
                }
                Component::DeclareDataProperty(_) => Some(NamedEntityKind::DataProperty),
                Component::DeclareDatatype(_) => Some(NamedEntityKind::Datatype),
                Component::DeclareNamedIndividual(_) => Some(NamedEntityKind::NamedIndividual),
                _ => None,
            },
            _ => None,
        }
    }

    fn aa_to_iri(&self, ax: &AnnotatedComponent<A>) -> Option<IRI<A>> {
        match ax.kind() {
            ComponentKind::DeclareClass
            | ComponentKind::DeclareObjectProperty
            | ComponentKind::DeclareAnnotationProperty
            | ComponentKind::DeclareDataProperty
            | ComponentKind::DeclareDatatype
            | ComponentKind::DeclareNamedIndividual => match &ax.component {
                Component::DeclareClass(dc) => Some(dc.0.0.clone()),
                Component::DeclareObjectProperty(op) => Some(op.0.0.clone()),
                Component::DeclareAnnotationProperty(ap) => Some(ap.0.0.clone()),
                Component::DeclareDataProperty(dp) => Some(dp.0.0.clone()),
                Component::DeclareDatatype(dt) => Some(dt.0.0.clone()),
                Component::DeclareNamedIndividual(ni) => Some(ni.0.0.clone()),
                _ => None,
            },
            _ => None,
        }
    }
}

macro_rules! some {
    ($body:expr) => {
        (|| Some($body))()
    };
}

impl<A, AA> Default for DeclarationMappedIndex<A, AA> {
    fn default() -> Self {
        DeclarationMappedIndex {
            kinds: Default::default(),
            declared: Default::default(),
            puns: Default::default(),
            pd: Default::default(),
        }
    }
}

impl<A: ForIRI, AA: ForIndex<A>> OntologyIndex<A, AA> for DeclarationMappedIndex<A, AA> {
    fn index_insert(&mut self, ax: AA) -> bool {
        some! {
            {
                let ne = self.aa_to_ne(ax.borrow())?;
                let iri = self.aa_to_iri(ax.borrow())?;

                let declared = self.declared.entry(iri.clone()).or_default();
                if !declared.contains(&ne) {
                    declared.push(ne);
                }

                // If this is a individual and we already have a
                // class, this is a pun, and we ignore the NI
                if ne == NamedEntityKind::NamedIndividual &&
                    self.kinds.get(&iri) == Some(&NamedEntityKind::Class)
                {
                    self.puns.insert(iri.clone());
                    return None;
                }

                // AnnotationProperty/ObjectProperty (or DataProperty)
                // punning is not legal in OWL 2 DL, but happens. We
                // pick Object or DataProperty here, the resolution
                // will depend on implementation details.
                if ne == NamedEntityKind::AnnotationProperty
                    && matches!(
                        self.kinds.get(&iri),
                        Some(NamedEntityKind::ObjectProperty) | Some(NamedEntityKind::DataProperty)
                    )
                {
                    return None;
                }

                // Save the kind
                let s = self.kinds.insert(iri.clone(), ne);

                // If we have replaced an NI with a class, we have a pun
                if ne == NamedEntityKind::Class &&
                    s == Some(NamedEntityKind::NamedIndividual)
                {
                    self.puns.insert(iri);
                }

                s
            }
        }
        .is_some()
    }

    fn index_remove(&mut self, ax: &AnnotatedComponent<A>) -> bool {
        let s = some! {
            {
                let iri = self.aa_to_iri(ax)?;
                if let (Some(ne), Some(declared)) = (self.aa_to_ne(ax), self.declared.get_mut(&iri)) {
                    declared.retain(|k| *k != ne);
                    if declared.is_empty() {
                        self.declared.remove(&iri);
                    }
                }
                self.kinds.remove(&iri)
            }
        };

        s.is_some()
    }
}

impl DeclarationMappedIndex<RcStr, RcAnnotatedComponent> {
    pub fn new_rc() -> Self {
        Self::default()
    }
}

#[cfg(test)]
mod test {
    use super::DeclarationMappedIndex;
    use crate::model::{AnnotatedComponent, Build, NamedOWLEntity, NamedOWLEntityKind, RcStr};
    use crate::ontology::indexed::OntologyIndex;
    use crate::vocab::OWL;
    fn stuff() -> (
        AnnotatedComponent<RcStr>,
        AnnotatedComponent<RcStr>,
        AnnotatedComponent<RcStr>,
    ) {
        let b = Build::new_rc();
        let c: NamedOWLEntity<_> = b.class("http://www.example.com/c").into();
        let o: NamedOWLEntity<_> = b.object_property("http://www.example.com/p").into();
        let b: NamedOWLEntity<_> = b.data_property("http://www.example.com/d").into();

        (c.into(), o.into(), b.into())
    }

    #[test]
    fn test_cons() {
        let _d = DeclarationMappedIndex::new_rc();
    }

    #[test]
    fn test_insert() {
        let mut d = DeclarationMappedIndex::new_rc();
        let s = stuff();
        assert!(d.index_insert(s.0.into()));
        assert!(d.index_insert(s.1.into()));
        assert!(d.index_insert(s.2.into()));
    }

    #[test]
    fn test_punned_declaration_kinds() {
        let b = Build::new_rc();
        let iri = "http://www.example.com/p";
        for class_last in [false, true] {
            let mut d = DeclarationMappedIndex::new_rc();
            let class: NamedOWLEntity<_> = b.class(iri).into();
            let property: NamedOWLEntity<_> = b.object_property(iri).into();
            let (first, second) = if class_last {
                (property, class)
            } else {
                (class, property)
            };
            let first: AnnotatedComponent<RcStr> = first.into();
            let second: AnnotatedComponent<RcStr> = second.into();
            d.index_insert(first.into());
            d.index_insert(second.into());

            let iri = b.iri(iri);
            assert!(d.is_declared_as(&iri, NamedOWLEntityKind::Class));
            assert!(d.is_declared_as(&iri, NamedOWLEntityKind::ObjectProperty));
            assert!(!d.is_declared_as(&iri, NamedOWLEntityKind::DataProperty));
            assert_eq!(
                d.declaration_kind_preferring(&iri, &[NamedOWLEntityKind::ObjectProperty]),
                Some(NamedOWLEntityKind::ObjectProperty)
            );
            assert_eq!(
                d.declaration_kind_preferring(&iri, &[NamedOWLEntityKind::Class]),
                Some(NamedOWLEntityKind::Class)
            );
        }
    }

    #[test]
    fn test_declaration() {
        let mut d = DeclarationMappedIndex::new_rc();
        let s = stuff();
        assert!(d.index_insert(s.0.into()));
        assert!(d.index_insert(s.1.into()));
        assert!(d.index_insert(s.2.into()));

        let b = Build::new();
        assert_eq!(
            d.declaration_kind(&b.iri("http://www.example.com/c")),
            Some(NamedOWLEntityKind::Class)
        );

        assert!(d.is_declaration_kind(
            &b.iri("http://www.example.com/c"),
            NamedOWLEntityKind::Class
        ));

        assert_eq!(
            d.declaration_kind(&b.iri("http://www.example.com/p")),
            Some(NamedOWLEntityKind::ObjectProperty)
        );

        assert!(d.is_declaration_kind(
            &b.iri("http://www.example.com/p"),
            NamedOWLEntityKind::ObjectProperty
        ));

        assert_eq!(
            d.declaration_kind(&b.iri("http://www.example.com/d")),
            Some(NamedOWLEntityKind::DataProperty)
        );

        assert!(d.is_declaration_kind(
            &b.iri("http://www.example.com/d"),
            NamedOWLEntityKind::DataProperty
        ));
    }

    #[test]
    fn test_declaration_builtin() {
        let d = DeclarationMappedIndex::new_rc();
        let b = Build::new_rc();
        assert_eq!(
            d.declaration_kind(&b.iri(OWL::TopDataProperty.as_ref())),
            Some(NamedOWLEntityKind::DataProperty)
        );
    }

    #[test]
    fn test_pun_support() {
        let mut d = DeclarationMappedIndex::new_rc();
        let b = Build::new_rc();

        assert_eq!(d.puns().len(), 0);

        let iri = b.iri("http://www.example.com/p");
        let c: NamedOWLEntity<_> = b.class("http://www.example.com/p").into();
        let c: AnnotatedComponent<_> = c.into();
        let ni: NamedOWLEntity<_> = b.named_individual("http://www.example.com/p").into();
        let ni: AnnotatedComponent<_> = ni.into();

        d.index_insert(c.clone().into());
        d.index_insert(ni.clone().into());

        assert_eq!(d.puns().len(), 1);
        assert_eq!(d.puns().iter().next(), Some(&iri));
        assert_eq!(d.declaration_kind(&iri), Some(NamedOWLEntityKind::Class));
        assert_eq!(
            d.declaration_kind_prefer_punned_individual(&iri),
            Some(NamedOWLEntityKind::NamedIndividual)
        );

        let mut d = DeclarationMappedIndex::new_rc();
        d.index_insert(ni.clone().into());
        d.index_insert(c.clone().into());

        assert_eq!(d.puns().len(), 1);
        assert_eq!(d.puns().iter().next(), Some(&iri));
        assert_eq!(d.declaration_kind(&iri), Some(NamedOWLEntityKind::Class));
        assert_eq!(
            d.declaration_kind_prefer_punned_individual(&iri),
            Some(NamedOWLEntityKind::NamedIndividual)
        );
    }

    // Regression test for https://github.com/phillord/horned-owl/issues/228
    //
    // An IRI declared as both AnnotationProperty and ObjectProperty (illegal
    // punning under OWL 2 DL, but seen in real-world ontologies) must
    // resolve to the same declaration_kind() regardless of which
    // declaration was inserted first -- otherwise round-tripping through a
    // writer that reorders the declarations changes the resolved kind and
    // breaks reread.
    #[test]
    fn test_annotation_object_property_pun_order_independent() {
        let b = Build::new_rc();
        let iri = b.iri("http://www.example.com/p");
        let ap: AnnotatedComponent<_> = {
            let ap: NamedOWLEntity<_> = b.annotation_property("http://www.example.com/p").into();
            ap.into()
        };
        let op: AnnotatedComponent<_> = {
            let op: NamedOWLEntity<_> = b.object_property("http://www.example.com/p").into();
            op.into()
        };

        // AnnotationProperty declared first, ObjectProperty second.
        let mut d = DeclarationMappedIndex::new_rc();
        d.index_insert(ap.clone().into());
        d.index_insert(op.clone().into());
        assert_eq!(
            d.declaration_kind(&iri),
            Some(NamedOWLEntityKind::ObjectProperty)
        );

        // ObjectProperty declared first, AnnotationProperty second.
        let mut d = DeclarationMappedIndex::new_rc();
        d.index_insert(op.into());
        d.index_insert(ap.into());
        assert_eq!(
            d.declaration_kind(&iri),
            Some(NamedOWLEntityKind::ObjectProperty)
        );
    }

    // Same as above but for DataProperty rather than ObjectProperty.
    #[test]
    fn test_annotation_data_property_pun_order_independent() {
        let b = Build::new_rc();
        let iri = b.iri("http://www.example.com/p");
        let ap: AnnotatedComponent<_> = {
            let ap: NamedOWLEntity<_> = b.annotation_property("http://www.example.com/p").into();
            ap.into()
        };
        let dp: AnnotatedComponent<_> = {
            let dp: NamedOWLEntity<_> = b.data_property("http://www.example.com/p").into();
            dp.into()
        };

        let mut d = DeclarationMappedIndex::new_rc();
        d.index_insert(ap.clone().into());
        d.index_insert(dp.clone().into());
        assert_eq!(
            d.declaration_kind(&iri),
            Some(NamedOWLEntityKind::DataProperty)
        );

        let mut d = DeclarationMappedIndex::new_rc();
        d.index_insert(dp.into());
        d.index_insert(ap.into());
        assert_eq!(
            d.declaration_kind(&iri),
            Some(NamedOWLEntityKind::DataProperty)
        );
    }
}
