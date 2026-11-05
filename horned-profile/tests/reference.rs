//! Expressivity and profiles of small ontologies, one construct and position
//! at a time, against `dev/profile-reference/cases.tsv`.
//!
//! The expected values are the OWL API's (4.2.8 for the name, 5.5.1 for the
//! profiles; see `dev/profile-reference/README.md`) except where the last
//! column documents a deviation.

use horned_owl::io::ParserConfiguration;
use horned_owl::io::ofn::reader::read;
use horned_owl::model::{RcAnnotatedComponent, RcStr};
use horned_owl::ontology::set::SetOntology;
use horned_profile::{Analysis, Profile, conformant_profiles};

/// Declarations every case shares; the same as in `Reference.java`.
const DECLARATIONS: &str = "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q)) Declaration(ObjectProperty(:r))
Declaration(DataProperty(:d)) Declaration(DataProperty(:e))
Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
";

fn ontology(axioms: &str) -> SetOntology<RcStr> {
    let src = format!(
        "Prefix(:=<http://example.com/>)\n\
         Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
         Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\n\
         Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
         Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n\
         Ontology(<http://example.com/o>\n{DECLARATIONS}{axioms}\n)\n"
    );
    read(&mut src.as_bytes(), ParserConfiguration::default())
        .unwrap()
        .0
}

#[test]
fn cases_match_the_reference() {
    let cases = include_str!("../../dev/profile-reference/cases.tsv");
    let mut wrong = Vec::new();
    let mut count = 0;
    for line in cases
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
    {
        count += 1;
        let fields: Vec<&str> = line.split('\t').collect();
        let (axioms, name) = (fields[0], fields[1]);
        let expected: Vec<Profile> = [Profile::OWL2DL, Profile::EL, Profile::QL, Profile::RL]
            .into_iter()
            .zip(&fields[2..6])
            .filter(|(_, v)| **v == "T")
            .map(|(p, _)| p)
            .collect();

        let o = ontology(axioms);
        let mut analysis: Analysis<RcStr, RcAnnotatedComponent> = Analysis::from_ontology(&o);
        let actual_name = analysis.expressivity().to_string();
        let actual = analysis.profiles();
        if actual_name != name || actual != expected || conformant_profiles(&o) != expected {
            wrong.push(format!(
                "{axioms}: expected {name} {expected:?}, got {actual_name} {actual:?} \
                 (check: {:?})",
                conformant_profiles(&o)
            ));
        }
    }
    assert!(count > 200, "only {count} cases");
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
