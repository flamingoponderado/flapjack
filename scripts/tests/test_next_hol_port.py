#!/usr/bin/env python3
"""Unit tests for the HOL port candidate navigator."""

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "next-hol-port.py"
SPEC = importlib.util.spec_from_file_location("next_hol_port", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PORT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PORT
SPEC.loader.exec_module(PORT)


class NextHolPortTests(unittest.TestCase):
    def test_selects_untagged_declarations_before_goal_in_source_order(self):
        with tempfile.TemporaryDirectory() as directory:
            index = Path(directory) / "hol-index.tsv"
            index.write_text(
                "# cakeml_commit\ttest\n"
                "Definition\tbase_def\tpancake/proofs/exampleScript.sml:2-5\texample\n"
                "Definition\tported_def\tpancake/proofs/exampleScript.sml:8-9\texample\n"
                "Theorem\tgoal\tpancake/proofs/exampleScript.sml:12-20\texample\n"
                "Definition\tlater_def\tpancake/proofs/exampleScript.sml:22-24\texample\n"
            )
            declarations = PORT.read_index(index)
        tagged = PORT.read_mapping(
            "Flapjack/Example.lean:4\tported\t"
            "cakeml/pancake/proofs/exampleScript.sml\tported_def\n"
        )
        found, count = PORT.candidates(
            declarations, tagged, "pancake/proofs/exampleScript.sml", "goal", {"Definition"}
        )
        self.assertEqual([entry.name for entry in found], ["base_def"])
        self.assertEqual(count, 1)

    def test_rejects_unknown_goal(self):
        declaration = PORT.Declaration("Definition", "base_def", "pancake/example.sml", 2, 4)
        with self.assertRaisesRegex(ValueError, "expected one declaration"):
            PORT.candidates([declaration], set(), "pancake/example.sml", "missing", {"Definition"})

    def test_line_qualified_mapping_matches_only_the_named_declaration(self):
        source = "compiler/backend/proofs/exampleScript.sml"
        declarations = [
            PORT.Declaration("Theorem", "rebound", source, 10, 14),
            PORT.Declaration("Theorem", "rebound", source, 20, 24),
        ]
        tagged = PORT.read_mapping(
            "Flapjack/Example.lean:4\tported\tcakeml/" + source + "\trebound:10\n"
        )
        found, count = PORT.candidates(declarations, tagged, source, None, {"Theorem"})
        self.assertEqual([entry.start for entry in found], [20])
        self.assertEqual(count, 1)
        tagged |= PORT.read_mapping(
            "Flapjack/Example.lean:9\tportedAgain\tcakeml/" + source + "\trebound:20\n"
        )
        found, count = PORT.candidates(declarations, tagged, source, None, {"Theorem"})
        self.assertEqual(found, [])
        self.assertEqual(count, 2)

    def test_frontend_script_candidates_use_index_and_hol_mapping(self):
        source = "compiler/backend/proofs/source_to_flatProofScript.sml"
        declarations = [
            PORT.Declaration("Definition", "ported_def", source, 3, 7),
            PORT.Declaration("Theorem", "missing", source, 8, 12),
        ]
        tagged = PORT.read_mapping(
            "Flapjack/Example.lean:4\tported\t"
            "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml\tported_def\n"
        )
        self.assertEqual(PORT.source_path("cakeml/" + source), source)
        found, count = PORT.candidates(declarations, tagged, source, None, {"Theorem"})
        self.assertEqual([entry.name for entry in found], ["missing"])
        self.assertEqual(count, 1)

    def test_rejects_paths_outside_cakeml_or_without_script_extension(self):
        for source in ("../outside.sml", "/outside.sml", "cakeml/../outside.sml", "compiler/backend/file.lean"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                PORT.source_path(source)


if __name__ == "__main__":
    unittest.main()
