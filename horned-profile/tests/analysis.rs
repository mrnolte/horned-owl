//! `Analysis` kept up to date by inserts and removes agrees with a fresh
//! check of the same components.

use horned_owl::io::ParserConfiguration;
use horned_owl::io::ofn::reader::read;
use horned_owl::model::{AnnotatedComponent, MutableOntology, RcAnnotatedComponent, RcStr};
use horned_owl::ontology::set::SetOntology;
use horned_profile::{Analysis, Expressivity, Profile, Violation, check, conformant_profiles};
use proptest::prelude::*;

/// Components chosen to touch every rule: declarations, undeclared use,
/// punning, reserved vocabulary, simple properties (transitivity, chains,
/// inverses, equivalences), chain cycles, grammar of each profile, and
/// copies of one axiom with different annotations.
const POOL: &str = "
Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q)) Declaration(ObjectProperty(:r))
Declaration(DataProperty(:d)) Declaration(NamedIndividual(:a))
Declaration(Datatype(:A)) Declaration(DataProperty(:p)) Declaration(AnnotationProperty(rdf:type))
SubClassOf(:A :B)
SubClassOf(Annotation(rdfs:comment \"x\") :A :B)
SubClassOf(:A ObjectSomeValuesFrom(:p :B))
SubClassOf(:A ObjectUnionOf(:B :C))
SubClassOf(ObjectUnionOf(:B :C) :A)
SubClassOf(:A ObjectAllValuesFrom(:q :C))
SubClassOf(:A ObjectComplementOf(:B))
SubClassOf(:A ObjectMaxCardinality(1 :p))
SubClassOf(:A ObjectHasSelf(:q))
SubClassOf(:A ObjectSomeValuesFrom(ObjectInverseOf(:q) :B))
SubClassOf(:C :D)
FunctionalObjectProperty(:q)
IrreflexiveObjectProperty(:r)
TransitiveObjectProperty(:p)
TransitiveObjectProperty(:r)
SubObjectPropertyOf(:p :q)
SubObjectPropertyOf(:q :p)
EquivalentObjectProperties(:q :r)
InverseObjectProperties(:p :r)
SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)
SubObjectPropertyOf(ObjectPropertyChain(:r :q) :p)
DisjointObjectProperties(:p :r)
DataPropertyRange(:d xsd:string)
DataPropertyRange(:d xsd:double)
ClassAssertion(:A :a)
ObjectPropertyAssertion(:p :a :a)
NegativeObjectPropertyAssertion(:q :a :a)
DatatypeDefinition(xsd:short xsd:integer)
ObjectPropertyRange(:r :A)
ObjectPropertyRange(:q :A)
ObjectPropertyAssertion(:q :a _:x)
ObjectPropertyRange(:s :C)
SubObjectPropertyOf(ObjectPropertyChain(:p :r) :s)
";

fn pool() -> Vec<AnnotatedComponent<RcStr>> {
    let src = format!(
        "Prefix(:=<http://example.com/>)\n\
         Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
         Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\n\
         Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
         Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n\
         Ontology(<http://example.com/o>\n{POOL}\n)"
    );
    let (o, _): (SetOntology<RcStr>, _) =
        read(&mut src.as_bytes(), ParserConfiguration::default()).unwrap();
    let mut pool: Vec<_> = o.into_iter().collect();
    pool.sort();
    pool
}

/// The violations as sorted debug strings; chain cycles only as present or
/// not, because which cycles the search reports depends on hash order.
fn normalized(violations: &[Violation<RcStr>]) -> (Vec<String>, bool) {
    let mut out: Vec<String> = violations
        .iter()
        .filter(|v| !matches!(v, Violation::UseOfPropertyInChainCausingCycle { .. }))
        .map(|v| format!("{v:?}"))
        .collect();
    out.sort();
    let cycles = violations
        .iter()
        .any(|v| matches!(v, Violation::UseOfPropertyInChainCausingCycle { .. }));
    (out, cycles)
}

fn assert_agrees(analysis: &mut Analysis<RcStr, RcAnnotatedComponent>, members: &[bool]) {
    let pool = pool();
    let mut fresh: SetOntology<RcStr> = SetOntology::new();
    for (ac, member) in pool.iter().zip(members) {
        if *member {
            fresh.insert(ac.clone());
        }
    }
    assert_eq!(analysis.len(), fresh.iter().count());
    assert_eq!(analysis.expressivity(), Expressivity::of(&fresh));
    assert_eq!(analysis.profiles(), conformant_profiles(&fresh));
    for profile in [Profile::OWL2DL, Profile::EL, Profile::QL, Profile::RL] {
        assert_eq!(
            normalized(analysis.report(profile).violations()),
            normalized(check(&fresh, profile).violations()),
            "{profile:?}"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn incremental_analysis_equals_fresh_check(
        ops in prop::collection::vec((any::<bool>(), 0usize..64), 1..40),
        query_every in 1usize..5,
    ) {
        let pool = pool();
        let mut analysis: Analysis<RcStr, RcAnnotatedComponent> = Analysis::new();
        let mut members = vec![false; pool.len()];
        for (step, (insert, i)) in ops.into_iter().enumerate() {
            let i = i % pool.len();
            let ac = &pool[i];
            if insert {
                prop_assert_eq!(analysis.insert(ac.clone().into()), !members[i]);
                members[i] = true;
            } else {
                prop_assert_eq!(analysis.remove(ac), members[i]);
                members[i] = false;
            }
            if step % query_every == 0 {
                assert_agrees(&mut analysis, &members);
            }
        }
        assert_agrees(&mut analysis, &members);
    }
}

#[test]
fn removing_the_last_qualified_cardinality_brings_back_n_and_f() {
    let pool = pool();
    let find = |s: &str| {
        pool.iter()
            .find(|ac| format!("{:?}", ac.component).contains(s))
            .unwrap()
            .clone()
    };
    let mut analysis: Analysis<RcStr, RcAnnotatedComponent> = Analysis::new();
    analysis.insert(find("FunctionalObjectProperty").into());
    assert_eq!(analysis.expressivity().to_string(), "ALF");
    analysis.insert(find("ObjectMaxCardinality").into());
    assert_eq!(analysis.expressivity().to_string(), "ALN");
    analysis.remove(&find("ObjectMaxCardinality"));
    assert_eq!(analysis.expressivity().to_string(), "ALF");
}

#[test]
fn whole_ontology_and_inserted_components_agree() {
    let pool = pool();
    let mut o: SetOntology<RcStr> = SetOntology::new();
    for ac in &pool {
        o.insert(ac.clone());
    }
    let mut analysis: Analysis<RcStr, RcAnnotatedComponent> = Analysis::from_ontology(&o);
    assert_agrees(&mut analysis, &vec![true; pool.len()]);

    // The pool reaches every kind of rule, so the property test above means
    // something.
    let kinds: std::collections::BTreeSet<String> = [Profile::EL, Profile::QL, Profile::RL]
        .into_iter()
        .flat_map(|p| analysis.report(p).violations().to_vec())
        .map(|v| {
            format!("{v:?}")
                .split([' ', '{', '('])
                .next()
                .unwrap()
                .to_owned()
        })
        .collect();
    for kind in [
        "UseOfUndeclaredClass",
        "UseOfIllegalPunning",
        "UseOfReservedVocabulary",
        "UseOfNonSimplePropertyInObjectHasSelf",
        "UseOfNonSimplePropertyInCardinalityRestriction",
        "UseOfNonSimplePropertyInFunctionalPropertyAxiom",
        "UseOfNonSimplePropertyInIrreflexivePropertyAxiom",
        "UseOfNonSimplePropertyInDisjointPropertiesAxiom",
        "UseOfPropertyInChainCausingCycle",
        "UseOfBuiltinDatatypeInDatatypeDefinition",
        "UseOfNonSuperClassExpression",
        "UseOfNonSubClassExpression",
        "UseOfObjectPropertyInverse",
        "UseOfIllegalAxiomKind",
        "UseOfAnonymousIndividual",
        "UseOfPropertyChainWithoutRangeOnLastProperty",
    ] {
        assert!(kinds.contains(kind), "{kind} not reached: {kinds:?}");
    }
}
