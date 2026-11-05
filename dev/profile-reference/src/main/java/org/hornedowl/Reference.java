package org.hornedowl;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Collections;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.FileDocumentSource;
import org.semanticweb.owlapi.io.OWLOntologyDocumentSource;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.MissingImportHandlingStrategy;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.profiles.OWL2DLProfile;
import org.semanticweb.owlapi.profiles.OWL2ELProfile;
import org.semanticweb.owlapi.profiles.OWL2QLProfile;
import org.semanticweb.owlapi.profiles.OWL2RLProfile;
import org.semanticweb.owlapi.profiles.OWLProfile;
import org.semanticweb.owlapi.util.DLExpressivityChecker;

/**
 * Prints the DL name and whether the ontology is in OWL 2 DL, EL, QL and RL,
 * tab-separated, one line per input. Imports are not loaded.
 *
 * <p>Inputs are files, or with {@code --cases cases.tsv} the axioms in the
 * first column of each case, wrapped in {@link #prefix} and {@link #DECLARATIONS}
 * (the same wrapper as horned-profile's {@code tests/reference.rs}).
 */
public class Reference {
    /** Declarations every case shares. */
    static final String DECLARATIONS = "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n"
        + "Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q)) Declaration(ObjectProperty(:r))\n"
        + "Declaration(DataProperty(:d)) Declaration(DataProperty(:e))\n"
        + "Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n";

    static String prefix() {
        return "Prefix(:=<http://example.com/>)\n"
            + "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
            + "Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\n"
            + "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"
            + "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n";
    }

    public static void main(String[] args) throws Exception {
        if (args.length == 2 && args[0].equals("--cases")) {
            for (String line : Files.readAllLines(Paths.get(args[1]), StandardCharsets.UTF_8)) {
                if (line.startsWith("#") || line.isEmpty()) {
                    continue;
                }
                String axioms = line.split("\t")[0];
                String doc = prefix() + "Ontology(<http://example.com/o>\n" + DECLARATIONS + axioms + "\n)\n";
                System.out.println(axioms + "\t" + check(new StringDocumentSource(doc)));
            }
            return;
        }
        for (String path : args) {
            System.out.println(path + "\t" + check(new FileDocumentSource(new File(path))));
        }
    }

    static String check(OWLOntologyDocumentSource source) {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        File missing = new File("does-not-exist.owl");
        manager.getIRIMappers().clear();
        manager.getIRIMappers().add(iri -> IRI.create(missing));
        OWLOntologyLoaderConfiguration config = new OWLOntologyLoaderConfiguration()
            .setMissingImportHandlingStrategy(MissingImportHandlingStrategy.SILENT);
        try {
            OWLOntology o = manager.loadOntologyFromOntologyDocument(source, config);
            StringBuilder line = new StringBuilder(
                new DLExpressivityChecker(Collections.singleton(o)).getDescriptionLogicName());
            for (OWLProfile p : new OWLProfile[] {new OWL2DLProfile(), new OWL2ELProfile(),
                new OWL2QLProfile(), new OWL2RLProfile()}) {
                line.append('\t').append(p.checkOntology(o).isInProfile() ? 'T' : 'F');
            }
            return line.toString();
        } catch (Exception e) {
            return "error: " + e.getClass().getSimpleName();
        }
    }
}
