#!/usr/bin/env python3
"""Unit tests for the HOL dependency inventory and its index parser.

These run without the generated ``.hol-index/`` directory: the parser is
exercised on temporary SML sources and a temporary dependency graph so that a
regression in attribute stripping, section termination, or graph sanitisation
fails here first.
"""

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


TESTS_DIR = Path(__file__).resolve().parent
SCRIPTS = TESTS_DIR.parent


def _load(module_name: str, filename: str):
    spec = importlib.util.spec_from_file_location(module_name, SCRIPTS / filename)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


INDEX_HOL = _load("index_hol", "index-hol.py")
INVENTORY = _load("hol_dependency_inventory", "hol-dependency-inventory.py")


class HolTypeIndexTests(unittest.TestCase):
    def test_quoted_abbreviations_and_spans(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "fixtureScript.sml"
            path.write_text(
                "Theory fixture\n"
                "(* Type hidden = ``:num`` *)\n"
                "Type heu_data = ``:num#num#num#num#num``\n"
                "Type multiline = ``:\n num # bool\n``\n"
                "Type unicode = “:num_set # num_set” (* comment *)\n"
                "Theorem after = known\n"
            )
            entries, _, recognized = INDEX_HOL.parse_file(root, path)
            self.assertTrue(recognized)
            self.assertEqual([(e.kind, e.name, e.start, e.end) for e in entries], [
                ("Type", "heu_data", 3, 3),
                ("Type", "multiline", 4, 6),
                ("Type", "unicode", 7, 7),
                ("Theorem", "after", 8, 8),
            ])

    def test_actual_heu_data_source(self):
        root = SCRIPTS.parent / "cakeml"
        entries, _, _ = INDEX_HOL.parse_file(
            root, root / "compiler/backend/word_allocScript.sml")
        entry = next(e for e in entries if e.name == "heu_data")
        self.assertEqual((entry.kind, entry.start, entry.end), ("Type", 1262, 1262))


class HolRelnTupleIndexTests(unittest.TestCase):
    def test_unindented_nested_bindings_not_indexed(self):
        binding = "val (step_rules,step_ind,step_cases) = Hol_reln`step x y`;\n"
        for opening, closing in (("local\n", "in end;\n"),
                                 ("val x = let\n", "in 1 end;\n"),
                                 ("structure X = struct\n", "end;\n")):
            with self.subTest(opening=opening), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                path = root / "fixtureScript.sml"
                path.write_text("Theory fixture\n" + opening + binding + closing)
                entries, _, _ = INDEX_HOL.parse_file(root, path)
                self.assertFalse(any(e.name == "step_rules" for e in entries))

    def test_shared_names_and_span(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "fixtureScript.sml"
            path.write_text("Theory fixture\nval (step_rules,step_ind,step_cases) = Hol_reln`\n step x y\n`;\n")
            entries, _, recognized = INDEX_HOL.parse_file(root, path)
            self.assertTrue(recognized)
            self.assertEqual([(e.kind, e.name, e.start, e.end) for e in entries], [
                ("Theorem", "step_rules", 2, 4),
                ("Theorem", "step_ind", 2, 4),
                ("Theorem", "step_cases", 2, 4),
            ])

    def test_actual_source_agrees_with_reference_checker(self):
        import runpy
        checker = runpy.run_path(str(SCRIPTS / "check-hol-refs.py"))
        root = SCRIPTS.parent / "cakeml"
        path = root / "compiler/backend/reg_alloc/parmoveScript.sml"
        entries, _, _ = INDEX_HOL.parse_file(root, path)
        tuples = [e for e in entries if e.name in {
            "step_rules", "step_ind", "step_cases", "dstep_rules", "dstep_ind", "dstep_cases"
        }]
        self.assertEqual(len(tuples), 6)
        names = checker["hol_declaration_lines"](path, {})
        for entry in tuples:
            self.assertEqual(names[entry.name], [entry.start])
            self.assertEqual(entry.end, 37 if entry.name.startswith("step_") else 492)

    def test_tuple_binding_ends_previous_equality_declaration(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "fixtureScript.sml"
            path.write_text("Theory fixture\nTheorem previous = known\nval (step_rules,step_ind,step_cases) = Hol_reln`step x y`;\n")
            entries, _, _ = INDEX_HOL.parse_file(root, path)
            previous = next(e for e in entries if e.name == "previous")
            self.assertEqual(previous.end, 2)
            self.assertEqual(len(entries), 4)

    def test_arbitrary_tuple_not_indexed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "fixtureScript.sml"
            path.write_text("Theory fixture\nval (step_rules,step_ind,step_cases) = other_generator`step x y`;\n")
            entries, _, _ = INDEX_HOL.parse_file(root, path)
            self.assertEqual(entries, [])


def _write_script(root: Path, name: str, body: str) -> Path:
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    return path


class AncestorsParserTests(unittest.TestCase):
    def test_strips_attributes_and_stops_at_section_keyword(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = _write_script(
                root,
                "exampleScript.sml",
                "Theory example\n"
                "Ancestors\n"
                "  integer[qualified] words[qualified] string[qualified]\n"
                "  location[qualified]\n"
                "\n"
                "(* a comment line *)\n"
                "Datatype:\n"
                "  t = A | B\n"
                "End\n"
                "val _ = x + 1;\n",
            )
            _, dependencies, _ = INDEX_HOL.parse_file(root, path)
        self.assertEqual(
            dependencies,
            [
                ("example", "integer"),
                ("example", "words"),
                ("example", "string"),
                ("example", "location"),
            ],
        )

    def test_stops_at_unindented_line_without_section_keyword(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = _write_script(
                root,
                "exampleScript.sml",
                "Theory example\n"
                "Ancestors\n"
                "  alpha beta\n"
                "\n"
                "open Gamma\n"
                "val _ = alpha beta;\n",
            )
            _, dependencies, _ = INDEX_HOL.parse_file(root, path)
        self.assertEqual(dependencies, [("example", "alpha"), ("example", "beta")])

    def test_drops_non_identifier_tokens_from_body_scan(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = _write_script(
                root,
                "exampleScript.sml",
                "Theory example\n"
                "Ancestors\n"
                "  alpha\n"
                "  (\n"
                "  SOME(SOME, st.facts);\n",
            )
            _, dependencies, _ = INDEX_HOL.parse_file(root, path)
        self.assertEqual(dependencies, [("example", "alpha")])


class TheoryGraphTests(unittest.TestCase):
    def test_rejects_non_identifier_nodes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "theory-deps.txt"
            path.write_text("good -> fine\nbroken -> :\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                INVENTORY.load_theory_graph(path)

    def test_closure_is_transitive_and_cycle_safe(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "theory-deps.txt"
            path.write_text(
                "a -> b\na -> c\nb -> d\nc -> d\nd -> a\ne -> f\n",
                encoding="utf-8",
            )
            graph = INVENTORY.load_theory_graph(path)
        self.assertEqual(
            sorted(INVENTORY.theory_closure(graph, ["a"])), ["a", "b", "c", "d"]
        )
        self.assertEqual(sorted(INVENTORY.theory_closure(graph, ["e"])), ["e", "f"])


class QualifiedCitationTests(unittest.TestCase):
    """HOL writes qualified references as ``Theory$name``; the ``$`` keeps the
    two halves inside one identifier token, so the suffix must be resolved
    explicitly.  A suffix is only accepted when it names a real declaration."""

    def _edges(self, body: str):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "exampleScript.sml"
            path.write_text(body, encoding="utf-8")
            lines = body.count("\n") + 1
            declarations = [
                INVENTORY.Declaration(
                    "Theorem", "rootThm", "exampleScript.sml", 1, lines, "example"
                ),
                INVENTORY.Declaration(
                    "Definition", "targetDef", "exampleScript.sml", 99, 99, "other"
                ),
            ]
            cache = INVENTORY.SourceCache(root)
            return INVENTORY.citation_edges(declarations, cache)

    def test_plain_identifier_is_cited(self):
        edges, _names, resolved = self._edges(
            "Theory example\nTheorem rootThm:\n  targetDef x\n"
        )
        self.assertIn("targetDef", edges["rootThm"])
        self.assertEqual(resolved, 0)

    def test_resolves_dollar_qualified_citation(self):
        edges, _names, resolved = self._edges(
            "Theory example\nTheorem rootThm:\n  other$targetDef x\n"
        )
        self.assertIn("targetDef", edges["rootThm"])
        self.assertEqual(resolved, 1)

    def test_ignores_unknown_dollar_suffix(self):
        edges, names, resolved = self._edges(
            "Theory example\nTheorem rootThm:\n  other$missing x\n"
        )
        self.assertNotIn("missing", names)
        self.assertNotIn("targetDef", edges["rootThm"])
        self.assertEqual(resolved, 0)

    def test_ignores_unrecognised_theory_prefix(self):
        # ``notatheory`` is not a HOL theory in the index, so even though
        # ``targetDef`` is a real declaration the token is not a citation.
        edges, names, resolved = self._edges(
            "Theory example\nTheorem rootThm:\n  notatheory$targetDef x\n"
        )
        self.assertIn("targetDef", names)
        self.assertNotIn("targetDef", edges["rootThm"])
        self.assertEqual(resolved, 0)

    def test_qualified_candidates_helper(self):
        names = {"targetDef"}
        theories = {"other"}
        self.assertEqual(
            INVENTORY.qualified_candidates("other$targetDef", names, theories),
            ("targetDef",),
        )
        self.assertEqual(
            INVENTORY.qualified_candidates("targetDef", names, theories), ()
        )
        self.assertEqual(
            INVENTORY.qualified_candidates("other$missing", names, theories), ()
        )
        self.assertEqual(
            INVENTORY.qualified_candidates("notatheory$targetDef", names, theories),
            (),
        )


class CommittedReportTests(unittest.TestCase):
    REPORT = INVENTORY.ROOT / "docs" / "HOL-DEPENDENCY-INVENTORY.md"

    def test_report_is_validated(self):
        text = self.REPORT.read_text(encoding="utf-8")
        self.assertIn("## Validation", text)
        self.assertNotIn("**UNVALIDATED**", text)
        self.assertIn("All count invariants hold", text)


if __name__ == "__main__":
    unittest.main()
