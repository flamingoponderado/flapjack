"""Prospective source guard for the guarded first-order unifier theorem."""

import json
import contextlib
import io
import runpy
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
CHECKER = runpy.run_path(str(ROOT / "scripts/check-hol-refs.py"))
CHECK = CHECKER["unify_eq_tunify_observer_errors"]
CHECK_HOL = CHECKER["unify_eq_tunify_pinned_hol_errors"]
HOL_PATHS = CHECKER["UNIFY_EQ_TUNIFY_HOL_PATHS"]
PATHS = CHECKER["UNIFY_EQ_TUNIFY_SOURCE_PATHS"]
SOURCES = tuple((ROOT / path).read_text() for path in PATHS)
ROWS = json.loads((ROOT / "docs/HOL-THEOREM-MAP.json").read_text())
REF = ("HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml", "unify_eq_tunify")
ATTRIBUTE = (f'@[hol "{REF[0]}" "{REF[1]}"\n'
             '  (fmap_as_finite_support_guarded_option_observations := [s])]\n')


class GuardedUnifierSourceTest(unittest.TestCase):
    def check(self, sources=SOURCES, path=PATHS[0], ref=REF, binders=("s",), rows=ROWS):
        return CHECK(sources[0], path, ref, binders, sources, rows)

    def test_reviewed_sources_and_future_attribute(self):
        self.assertEqual(self.check(), [])
        tagged = SOURCES[0].replace("theorem specifiedUnifyEqAux", ATTRIBUTE + "theorem specifiedUnifyEqAux", 1)
        self.assertNotEqual(tagged, SOURCES[0])
        self.assertEqual(self.check(sources=(tagged, *SOURCES[1:])), [])
        doubled = tagged.replace(ATTRIBUTE, ATTRIBUTE + ATTRIBUTE, 1)
        self.assertTrue(self.check(sources=(doubled, *SOURCES[1:])))
        misplaced = SOURCES[0].replace("theorem specifiedUnifyEquation", ATTRIBUTE + "theorem specifiedUnifyEquation", 1)
        self.assertTrue(self.check(sources=(misplaced, *SOURCES[1:])))

    def test_exact_site_and_parameter(self):
        for args in ({"path": "Other.lean"}, {"ref": (REF[0], "other")},
                     {"binders": ("s", "extra")}, {"binders": ("other",)}):
            with self.subTest(args=args):
                self.assertTrue(self.check(**args))
        self.assertTrue(self.check(sources=SOURCES[:-1]))
        self.assertTrue(CHECK("not the source", PATHS[0], REF, ("s",), SOURCES, ROWS))

    def test_every_reviewed_source_is_pinned(self):
        for index, source in enumerate(SOURCES):
            changed = list(SOURCES)
            changed[index] = source + "\ndef alteredSource : Nat := 0\n"
            with self.subTest(path=PATHS[index]):
                self.assertTrue(self.check(sources=tuple(changed)))
        whitespace = ("\n" + SOURCES[0] + "\n-- an ordinary comment\n", *SOURCES[1:])
        self.assertEqual(self.check(sources=whitespace), [])

    def test_unique_reviewed_dependency_rows(self):
        for name in ("Term", "wfs", "vwalkEq", "uRWellFounded", "walkstarEq",
                     "ocEqVarsWalkstar", "ocWalking", "uP", "uREq", "uRSubterm",
                     "tcaThm", "uPImpSubtermUR", "uPSym", "uPFupdate", "walkToVar",
                     "walkstarWalk", "walkstarInd", "notFdomWalkstar"):
            row = next(row for row in ROWS if row.get("lean_name") == name and
                       row.get("lean_path", "").startswith("Flapjack/HOL/Unification/"))
            with self.subTest(missing=name):
                self.assertTrue(self.check(rows=[item for item in ROWS if item is not row]))
            with self.subTest(duplicate=name):
                self.assertTrue(self.check(rows=ROWS + [row]))
            changed = {**row, "statement_status": "pending_statement_review"}
            with self.subTest(status=name):
                self.assertTrue(self.check(rows=[changed if item is row else item for item in ROWS]))
            changed = {**row, "words_as_type_indexed_bitvec": True}
            with self.subTest(extra_qualifier=name):
                self.assertTrue(self.check(rows=[changed if item is row else item for item in ROWS]))
            for note in ("", "   ", "reviewed"):
                changed = {**row, "reviewer": note}
                with self.subTest(reviewer=name, note=note):
                    self.assertTrue(self.check(rows=[changed if item is row else item for item in ROWS]))

    def test_each_original_hol_source_is_checked(self):
        self.assertEqual(CHECK_HOL(ROOT), [])
        for path in HOL_PATHS:
            def changed(_root, current):
                return "source mismatch" if current == path else None
            with self.subTest(path=path), patch.dict(CHECK_HOL.__globals__,
                                                     {"hol_submodule_source_error": changed}):
                self.assertEqual(CHECK_HOL(ROOT), [f"{path}: source mismatch"])

    def test_main_runs_preflight_only_for_tagged_theorem(self):
        main = CHECKER["main"]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "cakeml/pancake").mkdir(parents=True)
            target = root / "Flapjack/HOL/Unification/UnifDef/Choice.lean"
            target.parent.mkdir(parents=True)
            target.write_text("-- no theorem tag\n")
            seen = []
            def preflight(current_root, _records):
                seen.append(current_root)
                return ["preflight test"]
            overrides = {"ROOT": root, "lean_files": lambda: [target],
                         "reachable_modules": lambda: set(),
                         "reals_rendering_names": lambda _: set(),
                         "unify_eq_tunify_preflight": preflight}
            def run():
                output = io.StringIO()
                with patch.dict(main.__globals__, overrides), contextlib.redirect_stderr(output):
                    status = main([])
                return status, output.getvalue()
            self.assertEqual(run()[0], 0)
            self.assertEqual(seen, [])
            target.write_text(ATTRIBUTE + "theorem specifiedUnifyEqAux : True := trivial\n")
            status, output = run()
            self.assertNotEqual(status, 0)
            self.assertIn("guarded unifier preflight: preflight test", output)
            self.assertEqual(seen, [root])
            declaration = "theorem specifiedUnifyEqAux : True := trivial\n"
            forms = (ATTRIBUTE.replace('@[hol ', '@[simp, hol ') + declaration,
                     declaration + ATTRIBUTE.replace('@[hol ', 'attribute [simp, hol ').rstrip() +
                     " specifiedUnifyEqAux\n")
            for source in forms:
                with self.subTest(source=source):
                    seen.clear()
                    target.write_text(source)
                    status, output = run()
                    self.assertNotEqual(status, 0)
                    self.assertIn("guarded unifier preflight: preflight test", output)
                    self.assertEqual(seen, [root])


if __name__ == "__main__":
    unittest.main()
