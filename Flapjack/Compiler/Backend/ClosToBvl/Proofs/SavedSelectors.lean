module

public import Flapjack.Compiler.Backend.ClosToBvl.Layout
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

@[expose] public section

/-! Selectors for stored partial-closure arguments. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Eta expansion of the last two arguments of a curried function. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ETA2_THM"]
theorem eta2Thm {α β γ δ ε ζ : Type} (f : α → β → γ → δ → ε → ζ)
    (a : α) (b : β) (c : γ) :
    (fun x y => f a b c x y) = f a b c := by
  rfl

/-- Taking the bounded suffix of an appended list discards the appended tail. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "take_drop_lemma"]
theorem takeDropLemma {α : Type} (stuff : List α) (remArgs : Nat) (argList : List α)
    (bound : argList.length > remArgs) :
    ((argList ++ stuff).drop (argList.length - (remArgs + 1))).take (remArgs + 1) =
      argList.drop (argList.length - (remArgs + 1)) := by
  have len : (argList.drop (argList.length - (remArgs + 1))).length = remArgs + 1 := by
    simp only [List.length_drop]
    omega
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  exact List.take_of_length_le (by omega)

/-- Evaluating the original list through its constructor cases returns the
same result as applying the function directly. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "list_CASE_same"]
theorem listCaseSame {α β : Type} (xs : List α) (P : List α → β) :
    xs.casesOn (P []) (fun x rest => P (x :: rest)) = P xs := by
  cases xs <;> rfl

/-- A bounded entry in a generated recursive-code layout has the
corresponding generated label. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "p_genlist"]
theorem pGenlist {α β : Type} (expsPs : List ((α × β) × Nat))
    (k : Nat) (n : α) (e : β) (p loc maxApp : Nat) :
    letI : Nonempty α := ⟨n⟩
    letI : Nonempty β := ⟨e⟩
    holEl k expsPs = ((n, e), p) ∧
      expsPs.map Prod.snd = (List.range expsPs.length).map (fun i => loc + numStubs maxApp + 2 * i) ∧
      k < expsPs.length →
    p = holEl k ((List.range expsPs.length).map (fun i => loc + numStubs maxApp + 2 * i)) := by
  let _ : Nonempty α := ⟨n⟩
  let _ : Nonempty β := ⟨e⟩
  intro ⟨entry, labels, bound⟩
  have entryEq : expsPs[k] = ((n, e), p) := by
    simpa only [holEl_eq_getElem k expsPs bound] using entry
  have mappedBound : k < (expsPs.map Prod.snd).length := by simpa using bound
  have generatedBound : k < ((List.range expsPs.length).map (fun i => loc + numStubs maxApp + 2 * i)).length := by
    simpa using bound
  rw [holEl_eq_getElem k _ generatedBound]
  have same : (expsPs.map Prod.snd)[k]'mappedBound =
      ((List.range expsPs.length).map (fun i => loc + numStubs maxApp + 2 * i))[k]'generatedBound := by
    have selected := congrArg (fun values : List Nat => values[k]?) labels
    rw [List.getElem?_eq_getElem mappedBound, List.getElem?_eq_getElem generatedBound] at selected
    exact Option.some.inj selected
  simpa only [List.getElem_map, entryEq] using same

namespace SavedSelectorsCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end SavedSelectorsCarrier

/-- Select a block suffix in reverse order after arbitrary prefixes. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_genlist_prev_args"
  (fmap_as_finite_support := [refs])]
theorem evaluateGenlistPrevArgs {C F : Type} (saved stored context : List BvlSem.Value)
    (tag : Nat) (rest : List BvlSem.Value) (s : Flapjack.Compiler.Backend.BvlSem.State C F) :
    BvlSem.evaluate ((List.range saved.length).map (fun i =>
      Bvl.Exp.op (.blockOp (.elemAt (i + stored.length))) [.var context.length])).reverse
      (context ++ .block tag (stored ++ saved) :: rest) s = (.val saved.reverse, s) := by
  have run : ∀ n, n ≤ saved.length →
      BvlSem.evaluate ((List.range n).map (fun i =>
        Bvl.Exp.op (.blockOp (.elemAt (i + stored.length))) [.var context.length])).reverse
        (context ++ .block tag (stored ++ saved) :: rest) s = (.val (saved.take n).reverse, s) := by
    intro n bound
    induction n with
    | zero => simp [BvlSem.evaluate]
    | succ n ih =>
      have smaller : n ≤ saved.length := by omega
      have indexBound : n < saved.length := by omega
      rw [List.range_succ, List.map_append, List.reverse_append]
      change BvlSem.evaluateTuple ([_] ++ _, context ++ .block tag (stored ++ saved) :: rest, s) = _
      rw [BvlProps.evaluateAppend]
      have elemRun : BvlSem.evaluate [.op (.blockOp (.elemAt (n + stored.length))) [.var context.length]]
          (context ++ .block tag (stored ++ saved) :: rest) s = (.val [saved[n]], s) := by
        simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock,
          indexBound, Nat.add_comm]
      simp only [BvlSem.evaluateTuple, elemRun, ih smaller]
      rw [← List.take_append_getElem indexBound, List.reverse_append]
      rfl
  simpa using run saved.length (by omega)

/-- Select stored closure arguments in reverse from a four-entry environment. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_genlist_prev_args1_simpl"
  (fmap_as_finite_support := [refs])]
theorem evaluateGenlistPrevArgs1Simpl {C F : Type} (saved : List BvlSem.Value)
    (x y : BvlSem.Value) (tag : Nat) (ptr arity original a : BvlSem.Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) :
    BvlSem.evaluate ((List.range saved.length).map (fun i =>
      Bvl.Exp.op (.blockOp (.elemAt (i + 3))) [.var 3])).reverse
      [x, y, a, .block tag (ptr :: arity :: original :: saved)] s = (.val saved.reverse, s) := by
  have h := evaluateGenlistPrevArgs saved [ptr, arity, original] [x, y, a] tag [] s
  simpa using h

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
