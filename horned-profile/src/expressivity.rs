//! Description logic expressivity, named the way the OWL API named it
//! before version 4.5.7 (and so the way Protégé shows it): `AL`, `ALC`,
//! `ALE+`, `SHOIN(D)`, `SROIQ(D)`, ...
//!
//! The name is syntactic: it lists the constructs the logical axioms use,
//! after the OWL API's simplification rules, not the least expressive
//! logic an equivalent ontology would need.
//!
//! [`Expressivity`] is a set of constructs, so the expressivity of a union
//! of ontologies (an import closure) is the [`union`](Expressivity::union)
//! of theirs.
//!
//! Deliberate differences from the OWL API:
//!
//! - The complement of a named class is atomic negation, which `AL`
//!   already has. The OWL API tests whether the *complement* is atomic,
//!   which it never is, so it always reports `C`.
//! - `DatatypeDefinition`, and `HasKey` with a data property, use data
//!   (`(D)`); the OWL API skips both axioms.
//! - `DisjointClasses` and `DisjointUnion` of named classes only need
//!   atomic negation (`A ⊑ ¬B`), not `C`; the OWL API always adds `C`.
//! - `ObjectOneOf` with one individual is a nominal, not a union (`U`), and
//!   `DifferentIndividuals` needs no union either; the OWL API adds `U` to
//!   both.

use std::fmt;

use horned_owl::model::{
    AsymmetricObjectProperty, ClassExpression, Component, DataRange, ForIRI,
    IrreflexiveObjectProperty, ObjectPropertyExpression, Ontology, PropertyExpression,
    ReflexiveObjectProperty, SubObjectPropertyExpression,
};
use horned_owl::vocab::{OWL, OWL2Datatype};

/// One letter (or group of letters) of a description logic name.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Construct {
    /// `S`: `ALC` with transitive roles.
    S,
    /// `AL`: intersection, atomic negation, universal and limited
    /// existential restrictions. Every name starts with `AL` or `S`.
    AL,
    /// `C`: complex concept negation.
    C,
    /// `U`: concept union.
    U,
    /// `E`: full existential restrictions.
    E,
    /// `R`: complex role inclusions, reflexivity, irreflexivity, role
    /// disjointness, asymmetry and self restrictions.
    R,
    /// `H`: role hierarchy.
    H,
    /// `O`: nominals.
    O,
    /// `I`: inverse roles.
    I,
    /// `N`: unqualified cardinality restrictions.
    N,
    /// `Q`: qualified cardinality restrictions.
    Q,
    /// `F`: functional roles.
    F,
    /// `+`: transitive roles.
    Transitive,
    /// `(D)`: data properties, datatypes or literals.
    D,
}

impl Construct {
    /// Every construct, in the order a name lists them.
    const ALL: [Construct; 14] = [
        Construct::S,
        Construct::AL,
        Construct::C,
        Construct::U,
        Construct::E,
        Construct::R,
        Construct::H,
        Construct::O,
        Construct::I,
        Construct::N,
        Construct::Q,
        Construct::F,
        Construct::Transitive,
        Construct::D,
    ];

    /// The construct as it appears in a name.
    pub fn as_str(self) -> &'static str {
        match self {
            Construct::S => "S",
            Construct::AL => "AL",
            Construct::C => "C",
            Construct::U => "U",
            Construct::E => "E",
            Construct::R => "R",
            Construct::H => "H",
            Construct::O => "O",
            Construct::I => "I",
            Construct::N => "N",
            Construct::Q => "Q",
            Construct::F => "F",
            Construct::Transitive => "+",
            Construct::D => "(D)",
        }
    }

    fn bit(self) -> u16 {
        1 << self as u16
    }
}

impl fmt::Display for Construct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The constructs the logical axioms of an ontology use.
///
/// [`Display`](fmt::Display) gives the description logic name.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Expressivity(u16);

impl Expressivity {
    /// The expressivity of `o`.
    pub fn of<A: ForIRI, O: Ontology<A>>(o: &O) -> Self {
        o.iter().fold(Self::default(), |e, ac| {
            e.union(Self::of_component(&ac.component))
        })
    }

    /// The constructs one component uses; nothing for declarations,
    /// annotation axioms and the ontology header.
    pub fn of_component<A: ForIRI>(c: &Component<A>) -> Self {
        let mut e = Self::default();
        e.component(c);
        e
    }

    /// The expressivity of the union of both ontologies.
    pub fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// The constructs of the name, in order, after simplification: `ALC`
    /// absorbs `E` and `U`, `Q` absorbs `N` and `F`, `S` replaces `ALC`
    /// with `+`, and `R` absorbs `H`.
    pub fn constructs(self) -> impl Iterator<Item = Construct> {
        let mut s = self.0 | Construct::AL.bit();
        let has = |s: u16, c: Construct| s & c.bit() != 0;
        if has(s, Construct::C) {
            s &= !(Construct::E.bit() | Construct::U.bit());
        } else if has(s, Construct::E) && has(s, Construct::U) {
            s = (s | Construct::C.bit()) & !(Construct::E.bit() | Construct::U.bit());
        }
        if has(s, Construct::N) || has(s, Construct::Q) {
            s &= !Construct::F.bit();
        }
        if has(s, Construct::Q) {
            s &= !Construct::N.bit();
        }
        if has(s, Construct::C) && has(s, Construct::Transitive) {
            s &= !(Construct::AL.bit() | Construct::C.bit() | Construct::Transitive.bit());
            s |= Construct::S.bit();
        }
        if has(s, Construct::R) {
            s &= !Construct::H.bit();
        }
        Construct::ALL.into_iter().filter(move |c| has(s, *c))
    }

    pub(crate) fn from_bits(bits: u16) -> Self {
        Self(bits)
    }

    pub(crate) fn bits(self) -> u16 {
        self.0
    }

    fn add(&mut self, c: Construct) {
        self.0 |= c.bit();
    }

    fn component<A: ForIRI>(&mut self, c: &Component<A>) {
        use Construct::*;
        match c {
            Component::SubClassOf(x) => {
                self.class(&x.sub);
                self.class(&x.sup);
            }
            Component::EquivalentClasses(x) => x.0.iter().for_each(|ce| self.class(ce)),
            // A ⊑ ¬B: atomic negation (in AL) when all operands are named.
            Component::DisjointClasses(x) => {
                if !all_named(&x.0) {
                    self.add(C);
                }
                x.0.iter().for_each(|ce| self.class(ce));
            }
            Component::DisjointUnion(x) => {
                self.add(U);
                if !all_named(&x.1) {
                    self.add(C);
                }
                x.1.iter().for_each(|ce| self.class(ce));
            }
            Component::SubObjectPropertyOf(x) => {
                match &x.sub {
                    SubObjectPropertyExpression::ObjectPropertyChain(chain) => {
                        self.add(R);
                        chain.iter().for_each(|p| self.object_property(p));
                    }
                    SubObjectPropertyExpression::ObjectPropertyExpression(p) => {
                        self.add(H);
                        self.object_property(p);
                    }
                }
                self.object_property(&x.sup);
            }
            Component::EquivalentObjectProperties(x) => {
                self.add(H);
                x.0.iter().for_each(|p| self.object_property(p));
            }
            Component::DisjointObjectProperties(x) => {
                self.add(R);
                x.0.iter().for_each(|p| self.object_property(p));
            }
            Component::InverseObjectProperties(_) => self.add(I),
            Component::ObjectPropertyDomain(x) => {
                self.class(&x.ce);
                self.object_property(&x.ope);
            }
            Component::ObjectPropertyRange(x) => {
                self.class(&x.ce);
                self.object_property(&x.ope);
            }
            Component::FunctionalObjectProperty(x) => {
                self.add(F);
                self.object_property(&x.0);
            }
            Component::InverseFunctionalObjectProperty(x) => {
                self.add(I);
                self.add(F);
                self.object_property(&x.0);
            }
            Component::ReflexiveObjectProperty(ReflexiveObjectProperty(p))
            | Component::IrreflexiveObjectProperty(IrreflexiveObjectProperty(p))
            | Component::AsymmetricObjectProperty(AsymmetricObjectProperty(p)) => {
                self.add(R);
                self.object_property(p);
            }
            Component::SymmetricObjectProperty(x) => {
                self.add(I);
                self.object_property(&x.0);
            }
            Component::TransitiveObjectProperty(x) => {
                self.add(Transitive);
                self.object_property(&x.0);
            }
            Component::SubDataPropertyOf(_) | Component::EquivalentDataProperties(_) => {
                self.add(H);
                self.add(D);
            }
            Component::FunctionalDataProperty(_) => {
                self.add(F);
                self.add(D);
            }
            Component::DisjointDataProperties(_)
            | Component::DataPropertyRange(_)
            | Component::DataPropertyAssertion(_)
            | Component::NegativeDataPropertyAssertion(_)
            | Component::DatatypeDefinition(_) => self.add(D),
            Component::DataPropertyDomain(x) => {
                self.add(D);
                self.class(&x.ce);
            }
            Component::HasKey(x) => {
                if x.vpe
                    .iter()
                    .any(|p| matches!(p, PropertyExpression::DataProperty(_)))
                {
                    self.add(D);
                }
            }
            Component::SameIndividual(_) => self.add(O),
            // {a} ⊑ ¬{b}: nominals and complex negation, no union.
            Component::DifferentIndividuals(_) => {
                self.add(O);
                self.add(C);
            }
            Component::ClassAssertion(x) => self.class(&x.ce),
            Component::ObjectPropertyAssertion(x) => self.object_property(&x.ope),
            Component::NegativeObjectPropertyAssertion(x) => self.object_property(&x.ope),
            _ => {}
        }
    }

    fn object_property<A: ForIRI>(&mut self, p: &ObjectPropertyExpression<A>) {
        if let ObjectPropertyExpression::InverseObjectProperty(_) = p {
            self.add(Construct::I);
        }
    }

    fn class<A: ForIRI>(&mut self, ce: &ClassExpression<A>) {
        use Construct::*;
        match ce {
            ClassExpression::Class(_) => {}
            ClassExpression::ObjectIntersectionOf(xs) | ClassExpression::ObjectUnionOf(xs) => {
                if let ClassExpression::ObjectUnionOf(_) = ce {
                    self.add(U);
                }
                xs.iter().for_each(|x| self.class(x));
            }
            ClassExpression::ObjectComplementOf(x) => {
                if !matches!(**x, ClassExpression::Class(_)) {
                    self.add(C);
                }
                self.class(x);
            }
            // One individual is a nominal; more are a union of nominals.
            ClassExpression::ObjectOneOf(xs) => {
                if xs.len() > 1 {
                    self.add(U);
                }
                self.add(O);
            }
            ClassExpression::ObjectSomeValuesFrom { ope, bce } => {
                if !is_thing(bce) {
                    self.add(E);
                }
                self.object_property(ope);
                self.class(bce);
            }
            ClassExpression::ObjectAllValuesFrom { ope, bce } => {
                self.object_property(ope);
                self.class(bce);
            }
            ClassExpression::ObjectHasValue { ope, .. } => {
                self.add(O);
                self.add(E);
                self.object_property(ope);
            }
            ClassExpression::ObjectHasSelf(ope) => {
                self.add(R);
                self.object_property(ope);
            }
            ClassExpression::ObjectMinCardinality { ope, bce, .. }
            | ClassExpression::ObjectMaxCardinality { ope, bce, .. }
            | ClassExpression::ObjectExactCardinality { ope, bce, .. } => {
                self.add(if is_thing(bce) { N } else { Q });
                self.object_property(ope);
                self.class(bce);
            }
            ClassExpression::DataSomeValuesFrom { .. } => {
                self.add(E);
                self.add(D);
            }
            ClassExpression::DataAllValuesFrom { .. } | ClassExpression::DataHasValue { .. } => {
                self.add(D)
            }
            ClassExpression::DataMinCardinality { dr, .. }
            | ClassExpression::DataMaxCardinality { dr, .. }
            | ClassExpression::DataExactCardinality { dr, .. } => {
                self.add(if is_literal(dr) { N } else { Q });
                self.add(D);
            }
        }
    }
}

fn all_named<A: ForIRI>(ces: &[ClassExpression<A>]) -> bool {
    ces.iter().all(|ce| matches!(ce, ClassExpression::Class(_)))
}

fn is_thing<A: ForIRI>(ce: &ClassExpression<A>) -> bool {
    matches!(ce, ClassExpression::Class(c) if c.0.as_ref() == OWL::Thing.as_ref())
}

fn is_literal<A: ForIRI>(dr: &DataRange<A>) -> bool {
    matches!(dr, DataRange::Datatype(d) if d.0.as_ref() == OWL2Datatype::Literal.as_ref())
}

impl fmt::Display for Expressivity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.constructs().try_for_each(|c| f.write_str(c.as_str()))
    }
}
