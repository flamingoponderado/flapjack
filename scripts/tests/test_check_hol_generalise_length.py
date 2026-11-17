"""Source checks for the generalization length qualifier."""

import json
import runpy
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER = runpy.run_path(str(ROOT / "scripts/check-hol-refs.py"))
CHECK = CHECKER["generalise_length_observer_errors"]
SITES = CHECKER["hol_attribute_sites"]
PATH = "Flapjack/Compiler/Inference/InferProps/Generalise.lean"
PRODUCER_PATH = "Flapjack/Compiler/Inference/Infer/Generalise.lean"
PRODUCER = "Flapjack.Compiler.Inference.Infer.Generalise.generaliseListMap"
REF = ("cakeml/compiler/inference/inferPropsScript.sml", "generalise_list_length")
SOURCE = (ROOT / PATH).read_text()
PRODUCER_SOURCE = (ROOT / PRODUCER_PATH).read_text()
ROWS = json.loads((ROOT / "docs/HOL-THEOREM-MAP.json").read_text())


class GeneraliseLengthSourceTest(unittest.TestCase):
    def test_qualifier_detection_handles_malformed_syntax(self):
        prefix = '@[hol "otherScript.sml" "other" '
        qualifier = "fmap_as_finite_support_parameter_tuple_observations"
        for suffix in (f"({qualifier} := malformed)]", f"({qualifier}) ({qualifier})]",
                       f"({qualifier} := (map_parameters := [subst, out]) "
                       f"(map_producer := {PRODUCER}) (result_component := component_2))]"):
            with self.subTest(suffix=suffix):
                sites = list(SITES([prefix + suffix], include_generalise_length=True))
                self.assertEqual(len(sites), 1)
                self.assertTrue(sites[0][-1])
        self.assertFalse(list(SITES(['@[hol "otherScript.sml" "other"]'],
                                    include_generalise_length=True))[0][-1])
        valid = (prefix + f"({qualifier} := (map_parameters := [subst, out]) "
                 f"(map_producer := {PRODUCER}) (result_component := component_2))]")
        self.assertEqual(list(SITES([valid], include_generalise_length=True))[0][-1],
                         ("subst", "out", PRODUCER, "component_2"))

    def check(self, source=SOURCE, path=PATH, ref=REF, params=("subst", "out"),
              producer=PRODUCER, component="component_2", producer_source=PRODUCER_SOURCE,
              rows=ROWS):
        return CHECK(source, path, ref, params, producer, component, producer_source, rows)

    def test_actual_statement_and_producer(self):
        self.assertEqual(self.check(), [])

    def test_wrong_qualifier_metadata(self):
        for args in ({"path": "Other.lean"}, {"ref": (REF[0], "other")},
                     {"params": ("out", "subst")}, {"producer": "generaliseListMap"},
                     {"component": "component_1"}):
            with self.subTest(args=args):
                self.assertTrue(self.check(**args))

    def test_statement_and_witness_mutations_fail(self):
        for source in (
            SOURCE.replace("(count, out, result)", "(count, subst, result)"),
            SOURCE.replace("result.length = input.length", "input.length = result.length"),
            SOURCE.replace("(result : List InferT)", "(result : List InferT) (extra : True)"),
            SOURCE.replace("(out : HolFiniteMapExact Nat Nat) (key : Nat)",
                           "(out : HolFiniteMapExact Nat Nat) (key : Nat) (extra : True)"),
            SOURCE.replace("open Flapjack.Compiler.Inference.Infer.Generalise", "open Other"),
            SOURCE.replace("open Flapjack.Compiler.Inference.Infer.Generalise\n",
                           "open Flapjack.Compiler.Inference.Infer.Generalise\n  Other.Namespace\n"),
            SOURCE.replace("public import Flapjack.FiniteMap.BroadCodec", "public import Other"),
            SOURCE.replace("public import Flapjack.FiniteMap.BroadCodec\n",
                           "public import Flapjack.FiniteMap.BroadCodec\n  Other.Module\n"),
            "import Other\n" + SOURCE,
            SOURCE + "\ndef generaliseListMap := 0\n",
        ):
            with self.subTest(source=source[-200:]):
                self.assertTrue(self.check(source=source))

    def test_producer_source_and_manifest_are_required(self):
        self.assertTrue(self.check(producer_source=PRODUCER_SOURCE.replace(
            "generaliseMap generaliseListMap", "generaliseMap other")))
        rows = [row for row in ROWS if not (row.get("lean_path") == PRODUCER_PATH and
                                            row.get("lean_name") == "generaliseListMap")]
        self.assertTrue(self.check(rows=rows))
        row = next(row for row in ROWS if row.get("lean_path") == PRODUCER_PATH and
                   row.get("lean_name") == "generaliseListMap")
        self.assertTrue(self.check(rows=ROWS + [row]))
        changed = [{**item, "statement_status": "reviewed_exact"} if item == row else item
                   for item in ROWS]
        self.assertTrue(self.check(rows=changed))
        changed = [{**item, "words_as_type_indexed_bitvec": True} if item == row else item
                   for item in ROWS]
        self.assertTrue(self.check(rows=changed))
        changed = [{**item, "hol_line": 151} if item == row else item for item in ROWS]
        self.assertTrue(self.check(rows=changed))


if __name__ == "__main__":
    unittest.main()
