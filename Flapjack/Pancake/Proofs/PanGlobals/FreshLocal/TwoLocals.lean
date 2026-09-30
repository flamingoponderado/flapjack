import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Assembly

namespace Flapjack.PanGlobalsTwoFreshLocals
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Full sequential two-fresh-locals theorem (HOL1087-1102).
Two applications of the full fresh-local result preserve source update order.
The names may coincide; no distinctness or extra evaluation premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_two_fresh_locals"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateTwoFreshLocalsHOL {width : Nat} {σ : Type} [NeZero width]
    (name1 : MlS) (value1 : ValueHOL width) (name2 : MlS) (value2 : ValueHOL width)
    (program : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name1 ∉ freeVarIdsHOL program ∧ name2 ∉ freeVarIdsHOL program ∧
      evaluateHOLFiniteState state program = (result, post)) :
    ∃ locals,
      evaluateHOLFiniteState
        {state with locals := (state.locals.updateEq (name1, value1)).updateEq (name2, value2)}
        program = (result, {post with locals := locals}) ∧
      (goodResHOL result = true ∧ result ≠ some .error →
        locals = (post.locals.updateEq (name1, value1)).updateEq (name2, value2)) := by
  obtain ⟨firstLocals, firstRun, firstGood⟩ :=
    PanGlobalsFreshLocalAssembly.evaluateFreshLocalHOL name1 value1 program state result post ⟨h.1, h.2.2⟩
  obtain ⟨locals, secondRun, secondGood⟩ :=
    PanGlobalsFreshLocalAssembly.evaluateFreshLocalHOL name2 value2 program
      {state with locals := state.locals.updateEq (name1, value1)}
      result {post with locals := firstLocals} ⟨h.2.1, firstRun⟩
  refine ⟨locals, secondRun, ?_⟩
  intro hg
  simpa only [firstGood hg] using secondGood hg

end Flapjack.PanGlobalsTwoFreshLocals
