"""The prospective nested-relation qualifier must reject vacuous witnesses."""

import runpy
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CHECKER = runpy.run_path(str(ROOT / "scripts/check-hol-refs.py"))
VALIDATE = runpy.run_path(str(ROOT / "scripts/hol_nested_relation_check.py"))["nested_relation_errors"]
RELATION = ROOT / "Flapjack/Compiler/Backend/ClosAnnotate/Proofs/ValueRelation.lean"


class NestedRelationShapeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = CHECKER["strip_lean_comments"](RELATION.read_text())

    def test_reviewed_shape(self):
        self.assertEqual(VALIDATE(self.source), [])

    def test_rejects_relation_and_witness_mutations(self):
        mutations = [
            ("inductive FunctionsRel", "def FunctionsRel"),
            ("inductive EnvOk", "inductive OtherEnvOk"),
            ("inductive ValueRel :", "abbrev Value := Unit\ninductive ValueRel :"),
            ("inductive ValueRel :", "opaque Value : Type\ninductive ValueRel :"),
            ("inductive ValueRel :", "local notation \"Value\" => Unit\ninductive ValueRel :"),
            ("| number (value : Int) : ValueRel (.number value) (.number value)",
             "| number (x y : Value) : ValueRel x y"),
            ("| number (value : Int)", "| arbitrary (x y : Value) : ValueRel x y\n  | number (value : Int)"),
            ("| outside (m l : Nat)", "| arbitrary (m l : Nat) (i : Spt Nat) (e f : List Value) (n : Nat) : EnvOk m l i e f n\n  | outside (m l : Nat)"),
            ("everyFnVarsNone [body] → env.length = m →", "env.length = m →"),
            ("shiftSource (altFreeSource [body]).1 m arity index = [nextBody] →", ""),
            ("List.Forall₂ ValueRel args nextArgs → index < functions.length →",
             "List.Forall₂ ValueRel args nextArgs →"),
            ("l + m ≤ n → EnvOk", "EnvOk"),
            ("ValueRel (@Flapjack.holEl Value ⟨unitValue⟩ n env) (@Flapjack.holEl Value ⟨unitValue⟩ n nextEnv) →", ""),
            ("ValueRel (@Flapjack.holEl Value ⟨unitValue⟩ n env) (@Flapjack.holEl Value ⟨unitValue⟩ (l + compact) nextEnv) →", ""),
            ("l ≤ n → n < l + m → n < l + m →", "l ≤ n → n < l + m →"),
            ("| nil (env nextEnv : List Value)", "| empty (env nextEnv : List Value)"),
            ("FunctionsRel env nextEnv count [] []", "FunctionsRel env nextEnv count [] [body]"),
            ("FunctionsRel env nextEnv count [] []", "FunctionsRel env nextEnv count [] [] → False"),
            ("| cons (env nextEnv : List Value)", "| extra : True\n  | cons (env nextEnv : List Value)"),
            ("FunctionsRel env nextEnv count functions nextFunctions →",
             "FunctionsRel env nextEnv (count + 1) functions nextFunctions →"),
            ("FunctionsRel env nextEnv functions.length functions nextFunctions →",
             "True ∧ FunctionsRel env nextEnv functions.length functions nextFunctions →"),
            ("theorem functionsRel_iff", "theorem renamedWitness"),
            ("(functions nextFunctions : List (Nat × ClosLang.Exp)) :\n    FunctionsRel",
             "(functions nextFunctions : List (Nat × ClosLang.Exp)) (h : True) :\n    FunctionsRel"),
            ("right.1 = left.1 ∧", "True ∧"),
            ("List.Forall₂ (fun left right => ∃ m i,", "List.Forall₂ (fun left right => True ∧ ∃ m i,"),
            ("EnvOk m 0 i env nextEnv (n - (left.1 + count))",
             "True"),
            ("everyFnVarsNone [left.2] ∧ env.length = m", "True"),
            ("functions nextFunctions := by", "functions functions := by"),
        ]
        for before, after in mutations:
            with self.subTest(before=before):
                self.assertIn(before, self.source)
                self.assertTrue(VALIDATE(self.source.replace(before, after, 1)))

    def test_formatting_does_not_change_shape(self):
        altered = self.source.replace("inductive FunctionsRel", "inductive\nFunctionsRel")
        self.assertEqual(VALIDATE(altered), [])


if __name__ == "__main__":
    unittest.main()
