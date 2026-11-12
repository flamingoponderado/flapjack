module

public import Flapjack.Compiler.Backend.ClosToBvl.Layout
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

@[expose] public section

/-! Selectors for stored partial-closure arguments. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

namespace SavedSelectorsCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end SavedSelectorsCarrier

/-- Select a complete block suffix after arbitrary stored and environment prefixes. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_genlist_prev_args_no_rev"
  (fmap_as_finite_support := [refs])]
theorem evaluateGenlistPrevArgsNoRev {C F : Type} (saved stored context : List BvlSem.Value)
    (tag : Nat) (rest : List BvlSem.Value) (s : Flapjack.Compiler.Backend.BvlSem.State C F) :
    BvlSem.evaluate ((List.range saved.length).map (fun i =>
      Bvl.Exp.op (.blockOp (.elemAt (i + stored.length))) [.var context.length]))
      (context ++ .block tag (stored ++ saved) :: rest) s = (.val saved, s) := by
  have run : ∀ n, n ≤ saved.length →
      BvlSem.evaluate ((List.range n).map (fun i =>
        Bvl.Exp.op (.blockOp (.elemAt (i + stored.length))) [.var context.length]))
        (context ++ .block tag (stored ++ saved) :: rest) s = (.val (saved.take n), s) := by
    intro n bound
    induction n with
    | zero => simp [BvlSem.evaluate]
    | succ n ih =>
      have smaller : n ≤ saved.length := by omega
      have indexBound : n < saved.length := by omega
      rw [List.range_succ, List.map_append]
      change BvlSem.evaluateTuple (_ ++ [_], context ++ .block tag (stored ++ saved) :: rest, s) = _
      rw [BvlProps.evaluateAppend]
      simp only [BvlSem.evaluateTuple, ih smaller]
      have elemRun : BvlSem.evaluate [.op (.blockOp (.elemAt (n + stored.length))) [.var context.length]]
          (context ++ .block tag (stored ++ saved) :: rest) s = (.val [saved[n]], s) := by
        simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock,
          indexBound, Nat.add_comm]
      rw [elemRun]
      simp only [List.take_append_getElem indexBound]
  simpa using run saved.length (by omega)

/-- Select every saved value after the three stored closure fields. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_genlist_prev_args1_no_rev"
  (fmap_as_finite_support := [refs])]
theorem evaluateGenlistPrevArgs1NoRev {C F : Type} (saved : List BvlSem.Value) (first : BvlSem.Value)
    (tag : Nat) (ptr arity original : BvlSem.Value) (args : List BvlSem.Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) :
    BvlSem.evaluate ((List.range saved.length).map (fun i =>
      Bvl.Exp.op (.blockOp (.elemAt (i + 3))) [.var (args.length + 1)]))
      (first :: (args ++ [.block tag (ptr :: arity :: original :: saved)])) s = (.val saved, s) := by
  have h := evaluateGenlistPrevArgsNoRev saved [ptr, arity, original] (first :: args) tag [] s
  simpa [Nat.add_comm] using h

end Flapjack.Compiler.Backend.ClosToBvl
