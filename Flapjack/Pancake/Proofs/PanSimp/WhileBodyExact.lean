import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace PanSimpWhileBodySupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end PanSimpWhileBodySupport

/-- Universal complete body-evaluation equality preserves the complete While
result. This follows the source clock induction, including Continue and Break;
no assumption on successful evaluation or on either body's syntax is added. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_while_body_same"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateWhileBodySameHOL {width : Nat} {σ : Type} [NeZero width]
    (body body' : ProgHOL width) (condition : ExpHOL width)
    (hbody : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state body = evaluateHOLFiniteState state body') :
    ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (.while condition body) =
        evaluateHOLFiniteState state (.while condition body') := by
  classical
  have aux : ∀ n (state : PanSemStateFiniteExact width σ), state.clock = n →
      evaluateHOLFiniteState state (.while condition body) =
        evaluateHOLFiniteState state (.while condition body') := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro state hclock
      rw [evaluateHOLFiniteState_while_fixClockRewrite,
        evaluateHOLFiniteState_while_fixClockRewrite]
      simp only [hbody]
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      have hbound := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body'
      generalize hout : evaluateHOLFiniteState (decClockHOLFinite state) body' = outcome
      rcases outcome with ⟨result, post⟩
      rw [hout] at hbound
      have hlt : post.clock < n := by
        simp only [decClockHOLFinite] at hbound
        omega
      cases result with
      | none => exact ih post.clock hlt post rfl
      | some result =>
        cases result <;> try rfl
        exact ih post.clock hlt post rfl
  intro state
  exact aux state.clock state rfl

end Flapjack
