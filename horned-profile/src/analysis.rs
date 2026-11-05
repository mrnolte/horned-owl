//! Expressivity and profile conformance of a set of components, kept up to
//! date as components are inserted and removed.
//!
//! The rules that look at one component alone are evaluated once per
//! insert and once per remove, and only counted. Declarations and entity
//! usage are counted per IRI and kind. The role hierarchy (the only global
//! input of the simple-property and regularity rules) is rebuilt from its
//! own axioms when one of them changes, at the next query; then only the
//! components that use a property whose status changed are checked again.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use horned_owl::model::{
    AnnotatedComponent, Component, ForIRI, IRI, NamedEntityKind, ObjectProperty,
    ObjectPropertyExpression, Ontology,
};
use horned_owl::ontology::indexed::ForIndex;

use crate::declared::{illegal_pun_kinds, is_builtin, is_reserved_declaration};
use crate::expressivity::Expressivity;
use crate::simple_property::SimplePropertyAnalysis;
use crate::{Profile, ProfileReport, Violation, el, owl2dl, ql, regularity, rl};

/// The kinds a declaration can be required for.
const DECLARED_KINDS: [NamedEntityKind; 5] = [
    NamedEntityKind::Class,
    NamedEntityKind::ObjectProperty,
    NamedEntityKind::DataProperty,
    NamedEntityKind::AnnotationProperty,
    NamedEntityKind::Datatype,
];

/// Incremental expressivity and profile analysis of a set of components.
///
/// ```
/// use horned_owl::model::{Build, DeclareClass, MutableOntology, RcAnnotatedComponent};
/// use horned_owl::ontology::set::SetOntology;
/// use horned_profile::{Analysis, Profile};
///
/// let b = Build::new_rc();
/// let mut o = SetOntology::new();
/// o.insert(DeclareClass(b.class("http://example.com/A")));
///
/// let mut analysis: Analysis<_, RcAnnotatedComponent> = Analysis::from_ontology(&o);
/// assert_eq!(analysis.expressivity().to_string(), "AL");
/// assert_eq!(
///     analysis.profiles(),
///     vec![Profile::OWL2DL, Profile::EL, Profile::QL, Profile::RL]
/// );
/// ```
pub struct Analysis<A: ForIRI, AA: ForIndex<A> = Rc<AnnotatedComponent<A>>> {
    members: HashSet<AA>,
    /// Components using each construct.
    constructs: [usize; 14],
    /// Violations of the rules that look at one component alone, per
    /// profile; `Profile::OWL2DL` only counts the OWL 2 DL rules, the others
    /// only their own.
    local: [usize; 4],
    /// Components using each IRI as each kind.
    used: HashMap<(IRI<A>, NamedEntityKind), usize>,
    /// Declarations of each IRI as each kind.
    declared: HashMap<IRI<A>, HashMap<NamedEntityKind, usize>>,
    undeclared: HashSet<(IRI<A>, NamedEntityKind)>,
    punned: HashSet<IRI<A>>,
    reserved: HashSet<IRI<A>>,
    /// The role hierarchy: the components `SimplePropertyAnalysis` reads.
    roles: HashSet<AA>,
    roles_changed: bool,
    simple: SimplePropertyAnalysis<A>,
    cycles: Vec<Vec<ObjectProperty<A>>>,
    /// Components requiring each property expression to be simple.
    requirers: HashMap<ObjectPropertyExpression<A>, HashSet<AA>>,
    /// Requirers not yet checked against `simple`.
    unchecked: HashSet<AA>,
    /// Violations of the simple-property rules among checked requirers.
    non_simple: usize,
}

impl<A: ForIRI, AA: ForIndex<A>> Default for Analysis<A, AA> {
    fn default() -> Self {
        Analysis {
            members: HashSet::new(),
            constructs: [0; 14],
            local: [0; 4],
            used: HashMap::new(),
            declared: HashMap::new(),
            undeclared: HashSet::new(),
            punned: HashSet::new(),
            reserved: HashSet::new(),
            roles: HashSet::new(),
            roles_changed: false,
            simple: SimplePropertyAnalysis::from_components(std::iter::empty()),
            cycles: Vec::new(),
            requirers: HashMap::new(),
            unchecked: HashSet::new(),
            non_simple: 0,
        }
    }
}

impl<A: ForIRI, AA: ForIndex<A>> Analysis<A, AA> {
    /// An analysis of no components.
    pub fn new() -> Self {
        Self::default()
    }

    /// An analysis of the components of `o`.
    pub fn from_ontology<O: Ontology<A>>(o: &O) -> Self {
        let mut analysis = Self::default();
        for ac in o.iter() {
            analysis.insert(AA::from(ac.clone()));
        }
        analysis
    }

    /// Adds `component`; `false` if it is already there.
    pub fn insert(&mut self, component: AA) -> bool {
        if self.members.contains(component.borrow()) {
            return false;
        }
        self.count(&component, true);
        self.members.insert(component);
        true
    }

    /// Removes `component`; `false` if it is not there.
    pub fn remove(&mut self, component: &AnnotatedComponent<A>) -> bool {
        match self.members.take(component) {
            Some(member) => {
                self.count(&member, false);
                true
            }
            None => false,
        }
    }

    /// The number of components.
    pub fn len(&self) -> usize {
        self.members.len()
    }

    /// `true` if there are no components.
    pub fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    /// The expressivity of the components.
    pub fn expressivity(&self) -> Expressivity {
        Expressivity::from_bits(
            self.constructs
                .iter()
                .enumerate()
                .filter(|(_, n)| **n > 0)
                .fold(0, |bits, (i, _)| bits | 1 << i),
        )
    }

    /// The profiles the components conform to, in the order of [`Profile`].
    pub fn profiles(&mut self) -> Vec<Profile> {
        self.update_roles();
        let dl = self.local[0] == 0
            && self.undeclared.is_empty()
            && self.punned.is_empty()
            && self.reserved.is_empty()
            && self.non_simple == 0
            && self.cycles.is_empty();
        if !dl {
            return Vec::new();
        }
        [Profile::OWL2DL, Profile::EL, Profile::QL, Profile::RL]
            .into_iter()
            .filter(|p| self.local[index(*p)] == 0)
            .collect()
    }

    /// Every violation of `profile`; the same as [`crate::check`] on an
    /// ontology of these components, in no particular order.
    pub fn report(&mut self, profile: Profile) -> ProfileReport<A> {
        self.update_roles();
        let mut violations = Vec::new();
        for member in &self.members {
            let ac = member.borrow();
            owl2dl::local_violations(ac, &mut violations);
            owl2dl::simple_property_violations_of(ac, &self.simple, &mut violations);
            profile_violations(profile, ac, &mut violations);
        }
        violations.extend(
            self.undeclared
                .iter()
                .map(|(iri, kind)| owl2dl::undeclared_violation(iri.clone(), *kind)),
        );
        for iri in &self.punned {
            violations.push(Violation::UseOfIllegalPunning {
                iri: iri.clone(),
                kinds: illegal_pun_kinds(&self.declared_kinds(iri))
                    .into_iter()
                    .map(owl2dl::kind_name)
                    .collect(),
            });
        }
        violations.extend(
            self.reserved
                .iter()
                .map(|iri| Violation::UseOfReservedVocabulary { iri: iri.clone() }),
        );
        violations.extend(self.cycles.iter().map(|cycle| {
            Violation::UseOfPropertyInChainCausingCycle {
                cycle: cycle.clone(),
            }
        }));
        ProfileReport::new(profile, violations)
    }

    /// Adds (`add`) or subtracts the contributions of `member`.
    fn count(&mut self, member: &AA, add: bool) {
        let ac: &AnnotatedComponent<A> = member.borrow();
        let step = |n: &mut usize, by: usize| {
            if add { *n += by } else { *n -= by }
        };

        let bits = Expressivity::of_component(&ac.component).bits();
        for (i, n) in self.constructs.iter_mut().enumerate() {
            if bits & 1 << i != 0 {
                step(n, 1);
            }
        }

        let mut violations = Vec::new();
        owl2dl::local_violations(ac, &mut violations);
        step(&mut self.local[0], violations.len());
        for profile in [Profile::EL, Profile::QL, Profile::RL] {
            violations.clear();
            profile_violations(profile, ac, &mut violations);
            step(&mut self.local[index(profile)], violations.len());
        }

        for key in owl2dl::entity_usage_of(ac) {
            let n = self.used.entry(key.clone()).or_default();
            step(n, 1);
            if *n == 0 {
                self.used.remove(&key);
            }
            self.update_declared(&key.0, key.1);
        }

        if let Some((iri, kind)) = declaration(&ac.component) {
            let kinds = self.declared.entry(iri.clone()).or_default();
            let n = kinds.entry(kind).or_default();
            step(n, 1);
            if *n == 0 {
                kinds.remove(&kind);
                if kinds.is_empty() {
                    self.declared.remove(&iri);
                }
            }
            for kind in DECLARED_KINDS {
                self.update_declared(&iri, kind);
            }
            let kinds = self.declared_kinds(&iri);
            update(
                &mut self.punned,
                &iri,
                !illegal_pun_kinds(&kinds).is_empty(),
            );
            update(
                &mut self.reserved,
                &iri,
                !kinds.is_empty() && is_reserved_declaration(&iri, &kinds),
            );
        }

        if is_role_axiom(&ac.component) {
            if add {
                self.roles.insert(member.clone());
            } else {
                self.roles.remove(ac);
            }
            self.roles_changed = true;
        }

        let required = owl2dl::simple_property_requirements(ac);
        if required.is_empty() {
            return;
        }
        for ope in required {
            let requirers = self.requirers.entry(ope.clone()).or_default();
            if add {
                requirers.insert(member.clone());
            } else {
                requirers.remove(ac);
                if requirers.is_empty() {
                    self.requirers.remove(&ope);
                }
            }
        }
        if add {
            self.unchecked.insert(member.clone());
        } else if !self.unchecked.remove(ac) {
            self.non_simple -= non_simple(ac, &self.simple);
        }
    }

    /// Rebuilds the role hierarchy if it changed and checks the requirers it
    /// affects, and those not checked yet.
    fn update_roles(&mut self) {
        if self.roles_changed {
            self.roles_changed = false;
            let simple = SimplePropertyAnalysis::from_components(
                self.roles.iter().map(|member| member.borrow()),
            );
            self.cycles =
                regularity::chain_cycles_of(self.roles.iter().map(|member| member.borrow()));
            let mut affected: HashSet<&AA> = HashSet::new();
            for ope in self
                .simple
                .composites()
                .symmetric_difference(simple.composites())
            {
                if let Some(requirers) = self.requirers.get(ope) {
                    affected.extend(
                        requirers
                            .iter()
                            .filter(|r| !self.unchecked.contains((*r).borrow())),
                    );
                }
            }
            for requirer in affected {
                let ac = requirer.borrow();
                self.non_simple -= non_simple(ac, &self.simple);
                self.non_simple += non_simple(ac, &simple);
            }
            self.simple = simple;
        }
        for requirer in self.unchecked.drain() {
            self.non_simple += non_simple(requirer.borrow(), &self.simple);
        }
    }

    fn declared_kinds(&self, iri: &IRI<A>) -> BTreeSet<NamedEntityKind> {
        self.declared
            .get(iri)
            .map(|kinds| kinds.keys().copied().collect())
            .unwrap_or_default()
    }

    /// Updates whether `iri` is used as `kind` without a declaration.
    fn update_declared(&mut self, iri: &IRI<A>, kind: NamedEntityKind) {
        let key = (iri.clone(), kind);
        let missing = self.used.contains_key(&key)
            && !is_builtin(iri, kind)
            && !self
                .declared
                .get(iri)
                .is_some_and(|kinds| kinds.contains_key(&kind));
        if missing {
            self.undeclared.insert(key);
        } else {
            self.undeclared.remove(&key);
        }
    }
}

impl<A: ForIRI, AA: ForIndex<A>> Extend<AA> for Analysis<A, AA> {
    fn extend<T: IntoIterator<Item = AA>>(&mut self, iter: T) {
        for component in iter {
            self.insert(component);
        }
    }
}

fn index(profile: Profile) -> usize {
    match profile {
        Profile::OWL2DL => 0,
        Profile::EL => 1,
        Profile::QL => 2,
        Profile::RL => 3,
    }
}

/// Pushes the violations of `ac` against the rules `profile` adds to OWL 2
/// DL that look at one component alone.
fn profile_violations<A: ForIRI>(
    profile: Profile,
    ac: &AnnotatedComponent<A>,
    out: &mut Vec<Violation<A>>,
) {
    match profile {
        Profile::OWL2DL => {}
        Profile::EL => el::check_axiom(ac, out),
        Profile::QL => ql::check_axiom(ac, out),
        Profile::RL => rl::check_axiom(ac, out),
    }
}

fn non_simple<A: ForIRI>(ac: &AnnotatedComponent<A>, simple: &SimplePropertyAnalysis<A>) -> usize {
    let mut violations = Vec::new();
    owl2dl::simple_property_violations_of(ac, simple, &mut violations);
    violations.len()
}

fn update<A: ForIRI>(set: &mut HashSet<IRI<A>>, iri: &IRI<A>, member: bool) {
    if member {
        set.insert(iri.clone());
    } else {
        set.remove(iri);
    }
}

fn declaration<A: ForIRI>(c: &Component<A>) -> Option<(IRI<A>, NamedEntityKind)> {
    let (iri, kind) = match c {
        Component::DeclareClass(x) => (&x.0.0, NamedEntityKind::Class),
        Component::DeclareObjectProperty(x) => (&x.0.0, NamedEntityKind::ObjectProperty),
        Component::DeclareDataProperty(x) => (&x.0.0, NamedEntityKind::DataProperty),
        Component::DeclareAnnotationProperty(x) => (&x.0.0, NamedEntityKind::AnnotationProperty),
        Component::DeclareDatatype(x) => (&x.0.0, NamedEntityKind::Datatype),
        Component::DeclareNamedIndividual(x) => (&x.0.0, NamedEntityKind::NamedIndividual),
        _ => return None,
    };
    Some((iri.clone(), kind))
}

fn is_role_axiom<A: ForIRI>(c: &Component<A>) -> bool {
    matches!(
        c,
        Component::TransitiveObjectProperty(_)
            | Component::SubObjectPropertyOf(_)
            | Component::EquivalentObjectProperties(_)
            | Component::InverseObjectProperties(_)
    )
}

#[cfg(test)]
mod test {
    use super::Analysis;
    use horned_owl::model::{
        AnnotatedComponent, Build, ClassExpression, DeclareClass, FunctionalObjectProperty,
        ObjectPropertyExpression, RcStr, SubClassOf, TransitiveObjectProperty,
    };

    fn ac(c: impl Into<horned_owl::model::Component<RcStr>>) -> AnnotatedComponent<RcStr> {
        AnnotatedComponent::from(c.into())
    }

    #[test]
    fn class_axioms_leave_the_role_hierarchy_alone() {
        let b = Build::new_rc();
        let p: ObjectPropertyExpression<_> = b.object_property("http://example.com/p").into();
        let mut analysis: Analysis<RcStr> = Analysis::new();
        analysis.insert(ac(TransitiveObjectProperty(p.clone())).into());
        analysis.insert(ac(FunctionalObjectProperty(p.clone())).into());
        assert!(analysis.profiles().is_empty());
        assert!(!analysis.roles_changed);

        let a: ClassExpression<_> = b.class("http://example.com/A").into();
        analysis.insert(ac(DeclareClass(b.class("http://example.com/A"))).into());
        analysis.insert(
            ac(SubClassOf {
                sub: a.clone(),
                sup: a,
            })
            .into(),
        );
        assert!(!analysis.roles_changed);
        assert!(analysis.unchecked.is_empty());

        analysis.remove(&ac(TransitiveObjectProperty(p)));
        assert!(analysis.roles_changed);
        assert_eq!(analysis.non_simple, 1);
        analysis.profiles();
        assert_eq!(analysis.non_simple, 0);
    }
}
