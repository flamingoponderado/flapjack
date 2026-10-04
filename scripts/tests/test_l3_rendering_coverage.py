"""Fail closed on native body, signature, coverage and handwritten drift."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location("native_drift_tests",ROOT / "scripts/l3/check-renderings.py")
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

class NativeRenderingCoverage(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.actual=m.sources()
        cls.generated=m.renderings()
        cls.lock=json.loads(m.LOCK.read_text())

    def test_all_delivered_descendants_match_pinned_original(self):
        m.check(self.actual,self.generated,self.lock)
        for fragment in ("/MMU/", "/Defs/ReadInst.lean:", "/Step/Fetch.lean:", "/Defs/Decode.lean:", "/Defs/Run.lean:"):
            self.assertTrue(any(fragment in key for key in self.actual))

    def test_missing_extra_and_changed_generated_body_rejected(self):
        key="Flapjack/RiscV/L3/Defs/WritePC.lean:«write'PC»"
        variants=[{k:v for k,v in self.actual.items() if k!=key},
                  dict(self.actual,unexpected="def unexpected := true"),
                  dict(self.actual,**{key:self.actual[key].replace("state.procID","(BitVec.ofNat 8 0)")})]
        for actual in variants:
            with self.assertRaises(ValueError):m.check(actual,self.generated,self.lock)

    def test_each_handwritten_side_and_review_note_pinned(self):
        for key,exception in self.lock["exceptions"].items():
            actual=dict(self.actual)
            actual[key]+=" + changed"
            with self.subTest(key=key), self.assertRaises(ValueError):m.check(actual,self.generated,self.lock)
            lock=copy.deepcopy(self.lock)
            lock["exceptions"][key]["review_note"]=""
            with self.assertRaises(ValueError):m.check(self.actual,self.generated,lock)
            if exception["rendered_sha256"] is not None:
                generated=dict(self.generated)
                thy="riscv_step" if "/Step/" in key else "riscv"
                name=key.split(":",1)[1].strip("«»")
                body,nc=generated[thy,name]
                generated[thy,name]=(body+" changed",nc)
                with self.assertRaises(ValueError):m.check(self.actual,generated,self.lock)

    def test_only_recorded_computability_changes_allowed(self):
        actual=dict(self.actual)
        key=self.lock["noncomputable_overrides"][0]
        actual[key]="noncomputable " + actual[key] if not actual[key].startswith("noncomputable ") else actual[key].removeprefix("noncomputable ")
        with self.assertRaises(ValueError):m.check(actual,self.generated,self.lock)

    def test_next_uses_step_fetch_and_all_transfer_alternatives(self):
        key="Flapjack/RiscV/L3/Step/Next.lean:NextRISCV"
        original=self.generated["riscv_step","NextRISCV"][0]
        self.assertIn("riscv_step_Fetch",original)
        rendered,_=m.rendered_for(key,self.generated)
        self.assertIn("Fetch s",rendered)
        self.assertNotIn("riscv_Fetch",rendered)
        for constructor in ("BranchTo", "Trap"):
            self.assertIn("."+constructor,self.actual[key])
        # riscv-mi removes privileged returns (scripts/l3/riscv-mi-restriction.json).
        for constructor in ("Ereturn", "Mrts"):
            self.assertNotIn("."+constructor,self.actual[key])
        actual=dict(self.actual)
        actual[key]=actual[key].replace("Fetch s", "riscv_Fetch s",1)
        with self.assertRaises(ValueError):m.check(actual,self.generated,self.lock)

    def test_quoted_whitespace_not_erased(self):
        self.assertNotEqual(m.normalize('def f := "a b"'),m.normalize('def f := "ab"'))
        self.assertEqual(m.normalize('def f := 1'),m.normalize('def  f :=\n1'))

    def test_ci_discovers_each_fixture_checker(self):
        spec=importlib.util.spec_from_file_location("native_ci_tests",ROOT / "scripts/l3/check-native-model.py")
        ci=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ci)
        paths={c[1] for c in ci.commands()}
        self.assertTrue(set(self.lock["fixture_checkers"]) <= paths)
        self.assertIn("scripts/l3/check-renderings.py",paths)
        self.assertIn("scripts/l3/check-decode-fixtures.py",paths)
        self.assertIn("python3 scripts/l3/check-native-model.py",(ROOT / ".github/workflows/lean_action_ci.yml").read_text())
