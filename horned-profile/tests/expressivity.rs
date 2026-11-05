//! Description logic names, one construct at a time.

use horned_owl::io::ParserConfiguration;
use horned_owl::io::ofn::reader::read;
use horned_owl::model::RcStr;
use horned_owl::ontology::set::SetOntology;
use horned_profile::Expressivity;

fn ontology(axioms: &str) -> SetOntology<RcStr> {
    let src = format!(
        "Prefix(:=<http://example.com/>)\n\
         Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
         Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
         Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n\
         Ontology(<http://example.com/o>\n{axioms}\n)"
    );
    read(&mut src.as_bytes(), ParserConfiguration::default())
        .unwrap()
        .0
}

fn name(axioms: &str) -> String {
    Expressivity::of(&ontology(axioms)).to_string()
}

#[test]
fn names_follow_the_owl_api() {
    let cases = [
        ("", "AL"),
        (
            "Declaration(Class(:A)) AnnotationAssertion(rdfs:label :A \"A\")",
            "AL",
        ),
        ("SubClassOf(:A :B)", "AL"),
        ("SubClassOf(:A ObjectSomeValuesFrom(:p owl:Thing))", "AL"),
        ("SubClassOf(:A ObjectAllValuesFrom(:p :B))", "AL"),
        ("SubClassOf(:A ObjectSomeValuesFrom(:p :B))", "ALE"),
        ("SubClassOf(:A ObjectUnionOf(:B :C))", "ALU"),
        (
            "SubClassOf(:A ObjectUnionOf(:B ObjectSomeValuesFrom(:p :C)))",
            "ALC",
        ),
        (
            "SubClassOf(:A ObjectComplementOf(ObjectSomeValuesFrom(:p :C)))",
            "ALC",
        ),
        ("DisjointClasses(:A :B)", "ALC"),
        ("DisjointUnion(:A :B :C)", "ALC"),
        ("DifferentIndividuals(:a :b)", "ALCO"),
        ("SameIndividual(:a :b)", "ALO"),
        ("SubClassOf(:A ObjectOneOf(:a))", "ALUO"),
        ("SubClassOf(:A ObjectHasValue(:p :a))", "ALEO"),
        (
            "SubClassOf(:A ObjectSomeValuesFrom(ObjectInverseOf(:p) :B))",
            "ALEI",
        ),
        ("InverseObjectProperties(:p :q)", "ALI"),
        ("SymmetricObjectProperty(:p)", "ALI"),
        ("SubObjectPropertyOf(:p :q)", "ALH"),
        ("EquivalentObjectProperties(:p :q)", "ALH"),
        ("SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)", "ALR"),
        (
            "SubObjectPropertyOf(:p :q) SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)",
            "ALR",
        ),
        ("ReflexiveObjectProperty(:p)", "ALR"),
        ("IrreflexiveObjectProperty(:p)", "ALR"),
        ("AsymmetricObjectProperty(:p)", "ALR"),
        ("DisjointObjectProperties(:p :q)", "ALR"),
        ("SubClassOf(:A ObjectHasSelf(:p))", "ALR"),
        ("TransitiveObjectProperty(:p)", "AL+"),
        (
            "TransitiveObjectProperty(:p) SubClassOf(:A ObjectSomeValuesFrom(:p :B))",
            "ALE+",
        ),
        ("TransitiveObjectProperty(:p) DisjointClasses(:A :B)", "S"),
        ("FunctionalObjectProperty(:p)", "ALF"),
        ("InverseFunctionalObjectProperty(:p)", "ALIF"),
        ("SubClassOf(:A ObjectMaxCardinality(1 :p))", "ALN"),
        ("SubClassOf(:A ObjectMaxCardinality(1 :p owl:Thing))", "ALN"),
        (
            "FunctionalObjectProperty(:p) SubClassOf(:A ObjectMaxCardinality(1 :p))",
            "ALN",
        ),
        ("SubClassOf(:A ObjectMinCardinality(2 :p :B))", "ALQ"),
        (
            "SubClassOf(:A ObjectMinCardinality(2 :p :B)) SubClassOf(:A ObjectMaxCardinality(1 :p))",
            "ALQ",
        ),
        ("DataPropertyRange(:d xsd:string)", "AL(D)"),
        ("DataPropertyAssertion(:d :a \"1\")", "AL(D)"),
        ("SubClassOf(:A DataSomeValuesFrom(:d xsd:string))", "ALE(D)"),
        ("SubClassOf(:A DataAllValuesFrom(:d xsd:string))", "AL(D)"),
        ("SubClassOf(:A DataHasValue(:d \"1\"))", "AL(D)"),
        ("SubClassOf(:A DataMaxCardinality(1 :d))", "ALN(D)"),
        (
            "SubClassOf(:A DataMaxCardinality(1 :d rdfs:Literal))",
            "ALN(D)",
        ),
        (
            "SubClassOf(:A DataMaxCardinality(1 :d xsd:string))",
            "ALQ(D)",
        ),
        ("FunctionalDataProperty(:d)", "ALF(D)"),
        ("SubDataPropertyOf(:d :e)", "ALH(D)"),
        ("HasKey(:A () (:d))", "AL(D)"),
        ("HasKey(:A (:p) ())", "AL"),
        ("DatatypeDefinition(:t xsd:integer)", "AL(D)"),
        // The complement of a named class is atomic negation (OWL API: ALC).
        ("SubClassOf(:A ObjectComplementOf(:B))", "AL"),
        (
            "TransitiveObjectProperty(:p) SubObjectPropertyOf(:p :q) InverseObjectProperties(:p :r) \
             DisjointClasses(:A :B) SubClassOf(:A ObjectOneOf(:a)) \
             SubClassOf(:A ObjectMinCardinality(2 :p)) DataPropertyRange(:d xsd:string)",
            "SHOIN(D)",
        ),
        (
            "TransitiveObjectProperty(:p) SubObjectPropertyOf(:p :q) \
             SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r) InverseObjectProperties(:p :r) \
             DisjointClasses(:A :B) SubClassOf(:A ObjectOneOf(:a)) \
             SubClassOf(:A ObjectMinCardinality(2 :p :B)) DataPropertyRange(:d xsd:string)",
            "SROIQ(D)",
        ),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|(axioms, expected)| {
            let actual = name(axioms);
            (actual != *expected).then(|| format!("{axioms}: expected {expected}, got {actual}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn rules_and_axiom_annotations_add_nothing() {
    assert_eq!(
        name(
            "Annotation(rdfs:comment \"x\") SubClassOf(Annotation(rdfs:comment \"1\") :A :B) \
             DLSafeRule(Body(ClassAtom(:A Variable(:x))) Head(ClassAtom(:B Variable(:x))))"
        ),
        "AL"
    );
}

#[test]
fn the_union_of_two_ontologies_is_named_like_their_merge() {
    let e = Expressivity::of(&ontology("SubClassOf(:A ObjectSomeValuesFrom(:p :B))"));
    let u = Expressivity::of(&ontology("SubClassOf(:A ObjectUnionOf(:B :C))"));
    assert_eq!(e.to_string(), "ALE");
    assert_eq!(u.to_string(), "ALU");
    assert_eq!(e.union(u).to_string(), "ALC");
}
