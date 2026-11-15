module

public import Flapjack.Compiler.Backend.ClosToBvl.Layout
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

@[expose] public section

/-! Free-variable selectors for generated closure entries. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

namespace FreeLetCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end FreeLetCarrier

/-- Generated variables evaluate to a nonempty prefix of the environment. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_simple_genlist_vars"
  (fmap_as_finite_support := [refs])]
theorem evaluateSimpleGenlistVars {C F : Type} (env1 env2 : List BvlSem.Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) (_nonempty : 0 < env1.length) :
    BvlSem.evaluate ((List.range env1.length).map Bvl.Exp.var) (env1 ++ env2) s =
      (.val env1, s) := by
  have run := BvlProps.evaluateGenlistVars 0 (env1 ++ env2) env1.length s (by simp)
  simpa [BvlSem.evaluateTuple, List.take_append_of_le_length] using run

/-- A suffix of the supplied arguments evaluates as a generated variable list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cl_rel_run_lemma1"
  (fmap_as_finite_support := [refs])]
theorem clRelRunLemma1 {C F : Type} (numArgs : Nat) (args stuff : List BvlSem.Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) (bound : numArgs ≤ args.length) :
    BvlSem.evaluate ((List.range numArgs).map Bvl.Exp.var)
      (args.drop (args.length - numArgs) ++ stuff) s =
        (.val (args.drop (args.length - numArgs)), s) := by
  have suffixLength : (args.drop (args.length - numArgs)).length = numArgs := by
    simp only [List.length_drop]
    omega
  have run := BvlProps.evaluateGenlistVars 0 (args.drop (args.length - numArgs) ++ stuff)
    numArgs s (by simp [suffixLength])
  have takeEq : (args.drop (args.length - numArgs) ++ stuff).take numArgs =
      args.drop (args.length - numArgs) := by
    rw [List.take_append_of_le_length (by omega)]
    exact List.take_of_length_le (by omega)
  simpa only [BvlSem.evaluateTuple, Nat.add_zero, List.drop_zero, takeEq] using run

/-- A suffix followed by the closure evaluates as the generated variable list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cl_rel_run_lemma2"
  (fmap_as_finite_support := [refs])]
theorem clRelRunLemma2 {C F : Type} (numArgs : Nat) (args : List BvlSem.Value)
    (f : BvlSem.Value) (s : Flapjack.Compiler.Backend.BvlSem.State C F)
    (bound : numArgs ≤ args.length) :
    BvlSem.evaluate ((List.range (numArgs + 1)).map Bvl.Exp.var)
      (args.drop (args.length - numArgs) ++ [f]) s =
        (.val (args.drop (args.length - numArgs) ++ [f]), s) := by
  have suffixLength : (args.drop (args.length - numArgs)).length = numArgs := by
    simp only [List.length_drop]
    omega
  have run := evaluateSimpleGenlistVars (args.drop (args.length - numArgs) ++ [f]) [] s (by simp)
  simpa [suffixLength] using run

/-- Free selectors recover all fields following a block's two header values. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "bEval_free_let_Block"
  (fmap_as_finite_support := [refs])]
theorem bEval_freeLet_block {C F : Type} (fields : List BvlSem.Value) (x : Bvl.Exp)
    (env : List BvlSem.Value) (s : Flapjack.Compiler.Backend.BvlSem.State C F)
    (tag : Nat) (y z : BvlSem.Value)
    (clRun : BvlSem.evaluate [x] env s = (.val [.block tag (y :: z :: fields)], s)) :
    BvlSem.evaluate (freeLet x fields.length) env s = (.val fields, s) := by
  have run : ∀ n, n ≤ fields.length →
      BvlSem.evaluate (freeLet x n) env s = (.val (fields.take n), s) := by
    intro n bound
    induction n with
    | zero => simp [freeLet, BvlSem.evaluate]
    | succ n ih =>
      have boundN : n ≤ fields.length := by omega
      have indexBound : n < fields.length := by omega
      have elemRun : BvlSem.evaluate [.op (.blockOp (.elemAt (n + 2))) [x]] env s =
          (.val [fields[n]], s) := by
        rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, clRun]
        simp [BvlSem.doApp, BvlSem.applyBlock, indexBound]
      simp only [freeLet, List.range_succ, List.map_append, List.map_singleton]
      change BvlSem.evaluateTuple (freeLet x n ++ [.op (.blockOp (.elemAt (n + 2))) [x]], env, s) = _
      rw [BvlProps.evaluateAppend]
      simp only [BvlSem.evaluateTuple, ih boundN, elemRun, List.take_append_getElem indexBound]
  simpa using run fields.length (by omega)

end Flapjack.Compiler.Backend.ClosToBvl
