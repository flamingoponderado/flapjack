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
