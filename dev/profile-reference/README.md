# Reference values for horned-profile

`cases.tsv` lists small ontologies (one construct in one position each) with
their expected description logic name and OWL 2 profiles.
`horned-profile/tests/reference.rs` checks them without Java.

The expected values come from the OWL API:

- the name from **4.2.8**, the last release whose `DLExpressivityChecker`
  builds the classic names Protégé shows (`AL`, `SHOIN(D)`, `SROIQ(D)`);
  later releases concatenate internal construct labels (`RRESTR(D)`);
- the profiles from **5.5.1**.

Where the OWL API disagrees with the W3C specification
([OWL 2 Profiles](https://www.w3.org/TR/owl2-profiles/)), the W3C wins and the
last column says why:

| Case | OWL API | Here | Reason |
| --- | --- | --- | --- |
| `ObjectComplementOf(:B)` with a named class | `ALC` | `AL` | Atomic negation is part of `AL`. The OWL API tests whether the complement itself is atomic, which it never is. |
| `DatatypeDefinition`, `HasKey` with a data property | no `(D)` | `(D)` | Both use data; the OWL API skips the two axioms. |
| `DisjointClasses`, `DisjointUnion` of named classes | `C` | no `C` | `A ⊑ ¬B` is atomic negation, part of `AL`. |
| `ObjectOneOf` with one individual, `DifferentIndividuals` | `U` | no `U` | A single nominal is no union; `{a} ⊑ ¬{b}` needs none. |
| `DisjointClasses` with `ObjectSomeValuesFrom`, `ObjectUnionOf`, `ObjectOneOf`, `DataSomeValuesFrom` | not RL | RL | RL's `DisjointClasses` takes `subClassExpression`s (Profiles §4.2.5, §4.2.3). |
| a datatype the ontology declares or defines | not EL, QL, RL | EL, QL, RL | The grammars of all three profiles allow `DatatypeDefinition`; the lists of supported datatypes name the built-in ones. |

## Running the generator

Needs a JDK (11 or later) and Maven. 4.2.8 needs
`MAVEN_OPTS=--add-opens java.base/java.lang=ALL-UNNAMED`.

```sh
mvn -q compile exec:java -Dowlapi.version=4.2.8 "-Dexec.args=--cases cases.tsv"
mvn -q compile exec:java "-Dexec.args=--cases cases.tsv"
mvn -q compile exec:java "-Dexec.args=one.owl two.ttl"
mvn -q compile exec:java "-Dexec.args=--closure root.ttl http://example.com/lib=lib.owl"
```

Each prints one line per case or file: the input, the name, and `T`/`F` for
OWL 2 DL, EL, QL and RL. Imports are not
loaded; each case and file is checked alone. With `--closure`, the imports
listed as `iri=file` are read from those files (others stay missing), and the
name and profiles are of the import closure.
