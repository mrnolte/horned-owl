//! Expressivity and profile conformance of a set of components, kept up to
//! date as components are inserted and removed.
//!
//! The rules that look at one component alone are evaluated once per
//! insert and once per remove, and only counted. Declarations and entity
//! usage are counted per IRI and kind. The global rules keep their own
//! state and follow each change by what it touches:
//!
//! - simple properties ([`crate::roles`]): a role axiom carries a change of
//!   status up or down the role hierarchy from where it starts; then only
//!   the axioms that need a property whose status changed are checked again,
//!   and a new axiom that needs simple properties is checked against the
//!   status as it is;
//! - regularity: the graph of property chains is searched for cycles again,
//!   at the next query, only when a chain changed;
//! - EL's rule on chains and ranges ([`crate::chain_range`]): only the chains
//!   below a changed range or sub-property edge are checked again.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use horned_owl::model::{
    AnnotatedComponent, Component, ForIRI, IRI, NamedEntityKind, ObjectProperty,
    ObjectPropertyExpression, Ontology,
};
use horned_owl::ontology::indexed::ForIndex;

use crate::chain_range::ChainRanges;
use crate::declared::{illegal_pun_kinds, is_builtin, is_reserved_declaration};
use crate::expressivity::Expressivity;
use crate::roles::{RoleFacts, SimpleRoles, chain_edges};
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
    /// Declarations that only make entities declared: of each IRI as each
    /// kind, and the components.
    context: HashMap<IRI<A>, HashMap<NamedEntityKind, usize>>,
    context_members: HashSet<AA>,
    undeclared: HashSet<(IRI<A>, NamedEntityKind)>,
    punned: HashSet<IRI<A>>,
    reserved: HashSet<IRI<A>>,
    /// Which properties are composite.
    roles: SimpleRoles<A>,
    /// The edges of the property chain graph, counted.
    chain_edges: HashMap<(ObjectProperty<A>, ObjectProperty<A>), usize>,
    chains_changed: bool,
    cycles: Vec<Vec<ObjectProperty<A>>>,
    /// EL's rule on property chains and ranges.
    chain_ranges: ChainRanges<A, AA>,
    /// Components requiring each property expression to be simple.
    requirers: HashMap<ObjectPropertyExpression<A>, HashSet<AA>>,
    /// Violations of the simple-property rules.
    non_simple: usize,
    /// Requirers checked again because a property changed status (tests).
    #[cfg(test)]
    rechecked: usize,
}

impl<A: ForIRI, AA: ForIndex<A>> Default for Analysis<A, AA> {
    fn default() -> Self {
        Analysis {
            members: HashSet::new(),
            constructs: [0; 14],
            local: [0; 4],
            used: HashMap::new(),
            declared: HashMap::new(),
            context: HashMap::new(),
            context_members: HashSet::new(),
            undeclared: HashSet::new(),
            punned: HashSet::new(),
            reserved: HashSet::new(),
            roles: SimpleRoles::default(),
            chain_edges: HashMap::new(),
            chains_changed: false,
            cycles: Vec::new(),
            chain_ranges: ChainRanges::default(),
            requirers: HashMap::new(),
            non_simple: 0,
            #[cfg(test)]
            rechecked: 0,
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

    /// Adds the declaration `component` as context: it makes its entity
    /// declared, and counts for nothing else (the declarations of the imports
    /// of an ontology analysed by itself); `false` if it is already there or
    /// no declaration.
    pub fn insert_context(&mut self, component: AA) -> bool {
        let Some((iri, kind)) = declaration(&component.borrow().component) else {
            return false;
        };
        if self.context_members.contains(component.borrow()) {
            return false;
        }
        *self
            .context
            .entry(iri.clone())
            .or_default()
            .entry(kind)
            .or_default() += 1;
        self.context_members.insert(component);
        self.update_declared(&iri, kind);
        true
    }

    /// Removes the context declaration `component`; `false` if it is not
    /// there.
    pub fn remove_context(&mut self, component: &AnnotatedComponent<A>) -> bool {
        let Some(member) = self.context_members.take(component) else {
            return false;
        };
        if let Some((iri, kind)) = declaration(&member.borrow().component) {
            if let Some(kinds) = self.context.get_mut(&iri) {
                if let Some(n) = kinds.get_mut(&kind) {
                    *n -= 1;
                    if *n == 0 {
                        kinds.remove(&kind);
                    }
                }
                if kinds.is_empty() {
                    self.context.remove(&iri);
                }
            }
            self.update_declared(&iri, kind);
        }
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
        self.update_cycles();
        let dl = self.local[0] == 0
            && self.undeclared.is_empty()
            && self.punned.is_empty()
            && self.reserved.is_empty()
            && self.non_simple == 0
            && self.cycles.is_empty();
        if !dl {
            return Vec::new();
        }
        self.chain_ranges.update();
        [Profile::OWL2DL, Profile::EL, Profile::QL, Profile::RL]
            .into_iter()
            .filter(|p| self.local[index(*p)] == 0)
            .filter(|p| *p != Profile::EL || self.chain_ranges.count() == 0)
            .collect()
    }

    /// Every violation of `profile`; the same as [`crate::check`] on an
    /// ontology of these components, in no particular order: the
    /// [`local_violations`] of each component and the
    /// [`global_violations`](Self::global_violations).
    pub fn report(&mut self, profile: Profile) -> ProfileReport<A> {
        let mut violations: Vec<Violation<A>> = self
            .members
            .iter()
            .flat_map(|member| local_violations(profile, member.borrow()))
            .collect();
        violations.extend(self.global_violations(profile));
        ProfileReport::new(profile, violations)
    }

    /// The violations of `profile` that need the other components: simple
    /// properties, declarations, punning, reserved vocabulary, cycles of
    /// property chains and, for EL, ranges of property chains. Takes time in
    /// what violates, not in the number of components: with
    /// [`local_violations`] per component, a caller can tell violations as it
    /// finds them and these once the components are in.
    pub fn global_violations(&mut self, profile: Profile) -> Vec<Violation<A>> {
        self.update_cycles();
        let mut violations = Vec::new();
        let composite = |ope: &ObjectPropertyExpression<A>| self.roles.is_composite(ope);
        let requirers: HashSet<&AA> = self
            .requirers
            .iter()
            .filter(|(ope, _)| composite(ope))
            .flat_map(|(_, members)| members)
            .collect();
        for member in requirers {
            owl2dl::simple_property_violations_of(member.borrow(), &composite, &mut violations);
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
        if profile == Profile::EL {
            self.chain_ranges.update();
            violations.extend(self.chain_ranges.violations().cloned());
        }
        violations
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

        // A requirer going: its violations go, against the status as it is.
        let required = owl2dl::simple_property_requirements(ac);
        if !add && !required.is_empty() {
            self.non_simple -= self.non_simple_of(ac, &[]);
            for ope in &required {
                if let Some(requirers) = self.requirers.get_mut(ope) {
                    requirers.remove(ac);
                    if requirers.is_empty() {
                        self.requirers.remove(ope);
                    }
                }
            }
        }

        let facts = RoleFacts::of(&ac.component);
        if !facts.is_empty() {
            let changed = if add {
                self.roles.add(&facts)
            } else {
                self.roles.remove(&facts)
            };
            self.recheck(&changed);
        }

        for edge in chain_edges(&ac.component) {
            let n = self.chain_edges.entry(edge.clone()).or_default();
            step(n, 1);
            if *n == 0 {
                self.chain_edges.remove(&edge);
            }
            self.chains_changed = true;
        }

        if el::is_chain_range_input(&ac.component) {
            self.chain_ranges.change(member, add);
        }

        // A requirer coming: checked against the status as it is.
        if add && !required.is_empty() {
            for ope in required {
                self.requirers
                    .entry(ope)
                    .or_default()
                    .insert(member.clone());
            }
            self.non_simple += self.non_simple_of(ac, &[]);
        }
    }

    /// Checks again the requirers of the properties in `changed`, whose
    /// status just flipped.
    fn recheck(&mut self, changed: &[ObjectProperty<A>]) {
        if changed.is_empty() {
            return;
        }
        let mut affected: HashSet<AA> = HashSet::new();
        for p in changed {
            for ope in [
                ObjectPropertyExpression::ObjectProperty(p.clone()),
                ObjectPropertyExpression::InverseObjectProperty(p.clone()),
            ] {
                affected.extend(self.requirers.get(&ope).into_iter().flatten().cloned());
            }
        }
        for requirer in affected {
            let ac: &AnnotatedComponent<A> = requirer.borrow();
            self.non_simple -= self.non_simple_of(ac, changed);
            self.non_simple += self.non_simple_of(ac, &[]);
            #[cfg(test)]
            {
                self.rechecked += 1;
            }
        }
    }

    /// The simple-property violations of `ac` with the status as it was
    /// before the properties in `flipped` changed.
    fn non_simple_of(&self, ac: &AnnotatedComponent<A>, flipped: &[ObjectProperty<A>]) -> usize {
        let composite = |ope: &ObjectPropertyExpression<A>| {
            self.roles.is_composite(ope) != flipped.contains(&crate::roles::base(ope))
        };
        let mut violations = Vec::new();
        owl2dl::simple_property_violations_of(ac, &composite, &mut violations);
        violations.len()
    }

    /// Searches the property chain graph for cycles again if a chain changed.
    fn update_cycles(&mut self) {
        if self.chains_changed {
            self.chains_changed = false;
            let mut edges: HashMap<ObjectProperty<A>, HashSet<ObjectProperty<A>>> = HashMap::new();
            for (member, sup) in self.chain_edges.keys() {
                edges.entry(member.clone()).or_default().insert(sup.clone());
            }
            self.cycles = regularity::find_cycles(&edges);
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
                .is_some_and(|kinds| kinds.contains_key(&kind))
            && !self
                .context
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

/// The violations of `profile` that `ac` has by itself, whatever the other
/// components are: too few operands, a redefined built-in datatype and, for
/// EL, QL and RL, the grammar of the profile (a profile includes the rules of
/// OWL 2 DL). The rest comes from [`Analysis::global_violations`].
pub fn local_violations<A: ForIRI>(
    profile: Profile,
    ac: &AnnotatedComponent<A>,
) -> Vec<Violation<A>> {
    let mut violations = Vec::new();
    owl2dl::local_violations(ac, &mut violations);
    profile_violations(profile, ac, &mut violations);
    violations
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

#[cfg(test)]
mod test {
    use super::Analysis;
    use horned_owl::model::{
        AnnotatedComponent, Build, Component, FunctionalObjectProperty, ObjectPropertyExpression,
        RcStr, SubObjectPropertyExpression, SubObjectPropertyOf, TransitiveObjectProperty,
    };

    fn ac(c: impl Into<Component<RcStr>>) -> AnnotatedComponent<RcStr> {
        AnnotatedComponent::from(c.into())
    }

    fn ope(b: &Build<RcStr>, name: &str) -> ObjectPropertyExpression<RcStr> {
        b.object_property(format!("http://example.com/{name}"))
            .into()
    }

    #[test]
    fn a_role_change_rechecks_only_the_users_of_properties_whose_status_flipped() {
        let b = Build::new_rc();
        let (p, q) = (ope(&b, "p"), ope(&b, "q"));
        let mut analysis: Analysis<RcStr> = Analysis::new();
        analysis.insert(ac(FunctionalObjectProperty(p.clone())).into());
        analysis.insert(ac(FunctionalObjectProperty(q.clone())).into());

        // q becomes composite: only the axiom on q is checked again.
        analysis.insert(ac(TransitiveObjectProperty(q.clone())).into());
        assert_eq!((analysis.rechecked, analysis.non_simple), (1, 1));

        // A second reason for q flips nothing.
        let chain = ac(SubObjectPropertyOf {
            sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![p.clone(), p.clone()]),
            sup: q.clone(),
        });
        analysis.insert(chain.clone().into());
        assert_eq!(analysis.rechecked, 1);

        // q stays composite while the chain gives a reason.
        analysis.remove(&ac(TransitiveObjectProperty(q.clone())));
        assert_eq!((analysis.rechecked, analysis.non_simple), (1, 1));
        analysis.remove(&chain);
        assert_eq!((analysis.rechecked, analysis.non_simple), (2, 0));

        // A new axiom needing a simple property is checked against the status as it is.
        analysis.insert(ac(TransitiveObjectProperty(p.clone())).into());
        assert_eq!((analysis.rechecked, analysis.non_simple), (3, 1));
        assert!(analysis.profiles().is_empty());
    }

    #[test]
    fn local_violations_need_no_analysis_and_global_ones_are_the_rest() {
        use super::local_violations;
        use crate::Profile;
        use horned_owl::model::{ClassExpression, DeclareClass, DeclareObjectProperty, SubClassOf};
        let b = Build::new_rc();
        let p = b.object_property("http://example.com/p");
        let only = ac(SubClassOf {
            sub: ClassExpression::Class(b.class("http://example.com/A")),
            sup: ClassExpression::ObjectAllValuesFrom {
                ope: p.clone().into(),
                bce: Box::new(ClassExpression::Class(b.class("http://example.com/B"))),
            },
        });
        // `only` is outside EL by itself, before any other component is known.
        assert_eq!(local_violations(Profile::EL, &only).len(), 1);
        assert!(local_violations(Profile::OWL2DL, &only).is_empty());

        let mut analysis: Analysis<RcStr> = Analysis::new();
        for c in [
            only.clone(),
            ac(DeclareClass(b.class("http://example.com/A"))),
            ac(DeclareClass(b.class("http://example.com/B"))),
            ac(DeclareObjectProperty(p.clone())),
        ] {
            analysis.insert(c.into());
        }
        assert!(analysis.global_violations(Profile::EL).is_empty());
        assert_eq!(analysis.report(Profile::EL).violations().len(), 1);

        // A cardinality on a transitive property: global, it needs the property's status.
        analysis.insert(ac(TransitiveObjectProperty(p.clone().into())).into());
        analysis.insert(
            ac(SubClassOf {
                sub: ClassExpression::Class(b.class("http://example.com/A")),
                sup: ClassExpression::ObjectMaxCardinality {
                    n: 1,
                    ope: p.clone().into(),
                    bce: Box::new(ClassExpression::Class(b.class("http://example.com/B"))),
                },
            })
            .into(),
        );
        assert_eq!(analysis.global_violations(Profile::OWL2DL).len(), 1);
    }

    #[test]
    fn context_declarations_only_declare() {
        use crate::Profile;
        use horned_owl::model::{ClassExpression, DeclareClass, DeclareDatatype, SubClassOf};
        let b = Build::new_rc();
        let mut analysis: Analysis<RcStr> = Analysis::new();
        analysis.insert(
            ac(SubClassOf {
                sub: ClassExpression::Class(b.class("http://example.com/A")),
                sup: ClassExpression::Class(b.class("http://example.com/B")),
            })
            .into(),
        );
        assert!(analysis.profiles().is_empty(), "A and B are undeclared");
        for c in [
            ac(DeclareClass(b.class("http://example.com/A"))),
            ac(DeclareClass(b.class("http://example.com/B"))),
            ac(DeclareDatatype(
                b.datatype("http://www.w3.org/2001/XMLSchema#date"),
            )),
        ] {
            assert!(analysis.insert_context(c.into()));
        }
        assert_eq!(
            analysis.profiles(),
            vec![Profile::OWL2DL, Profile::EL, Profile::QL, Profile::RL]
        );
        assert!(analysis.report(Profile::EL).violations().is_empty());
        assert!(analysis.remove_context(&ac(DeclareClass(b.class("http://example.com/A")))));
        assert!(analysis.profiles().is_empty(), "A is undeclared again");
    }
}
