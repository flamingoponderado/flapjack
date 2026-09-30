import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsUnchangedLocalResults
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Original Return leaf of evaluate_unchanged_local. Successful results
fail the original good_res premise; no extra source-success assumption is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Return {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (expression : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.return expression) ∧
      evaluateHOLFiniteState state (.return expression) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_return] at heval
  repeat' split at heval
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  all_goals first | rfl | simp_all [goodResHOL]

/-- Original Raise leaf of evaluate_unchanged_local. Successful results
fail the original good_res premise; no extra source-success assumption is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Raise {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (exceptionId : MlS) (expression : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.raise exceptionId expression) ∧
      evaluateHOLFiniteState state (.raise exceptionId expression) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_raise] at heval
  cases hx : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression <;>
    cases hy : state.eshapes.lookup exceptionId
  all_goals simp only [hx, hy] at heval
  all_goals try
    (obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
     rfl)
  rename_i value shape
  by_cases hs : shapeOfHOLExact value = shape ∧
      sizeOfShapeWithContextHOL state.structs (shapeOfHOLExact value) ≤ 32
  · rw [if_pos hs] at heval
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
    simp [goodResHOL] at hgood
  · rw [if_neg hs] at heval
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
    rfl

end Flapjack.PanGlobalsUnchangedLocalResults
