import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.If
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsFreshLocalSeq
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

open Flapjack.PanGlobalsFreshLocalIf

/-- Genuine Seq induction case of HOL evaluate_fresh_local1045-1091. The IH
conjunction is the literal NONE-gated second child and unconditional first
child from evaluate_ind. The original predicate is unchanged; fix_clock is
removed by the reviewed evaluator equation rather than an assumed bound. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Seq {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (first second : ProgHOL width)
    (state : PanSemStateFiniteExact width σ)
    (ih :
      (∀ (firstResult : Option (PanSemResultExact width)) (middle : PanSemStateFiniteExact width σ),
        (firstResult, middle) = evaluateHOLFiniteState state first ∧ firstResult = none →
        freshLocalGoal name value second middle) ∧
      freshLocalGoal name value first state) :
    ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL (.seq first second) ∧
      evaluateHOLFiniteState state (.seq first second) = (result, post) →
      ∃ locals,
        evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
          (.seq first second) = (result, {post with locals := locals}) ∧
        (goodResHOL result = true ∧ result ≠ some .error →
          locals = post.locals.updateEq (name, value)) := by
  intro result post ⟨hfresh, heval⟩
  have hf : name ∉ freeVarIdsHOL first ∧ name ∉ freeVarIdsHOL second := by
    simpa only [freeVarIdsHOL, List.mem_append, not_or] using hfresh
  rw [evaluateHOLFiniteState_seq_line780] at heval
  have hex : ∃ r st, evaluateHOLFiniteState state first = (r, st) := ⟨_, _, rfl⟩
  obtain ⟨r, middle, hfirst⟩ := hex
  obtain ⟨middleLocals, hfirstFresh, hmiddle⟩ := ih.2 r middle ⟨hf.1, hfirst⟩
  cases r with
  | none =>
      simp only [hfirst] at heval
      have hml := hmiddle ⟨rfl, by simp⟩
      obtain ⟨locals, hsecondFresh, hlocals⟩ := ih.1 none middle
        ⟨hfirst.symm, rfl⟩ result post ⟨hf.2, heval⟩
      refine ⟨locals, ?_, hlocals⟩
      rw [evaluateHOLFiniteState_seq_line780, hfirstFresh]
      simpa only [hml] using hsecondFresh
  | some r =>
      simp only [hfirst] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      refine ⟨middleLocals, ?_, hmiddle⟩
      rw [evaluateHOLFiniteState_seq_line780, hfirstFresh]

end Flapjack.PanGlobalsFreshLocalSeq
