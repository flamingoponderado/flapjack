import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsUnchangedLocalWhile
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Original induction predicate, factored as infrastructure with no separate HOL original. -/
def unchangedLocalGoal {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (program : ProgHOL width) (state : PanSemStateFiniteExact width σ) : Prop :=
  ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
    name ∉ freeVarIdsHOL program ∧ evaluateHOLFiniteState state program = (result, post) ∧
    goodResHOL result = true ∧ result ≠ some .error →
    post.locals.lookup name = state.locals.lookup name

/-- While case with the literal three evaluate_ind IHs and unused value binder.
The reviewed fix_clock rewrite supplies clock behavior without an extra premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_While {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (condition : ExpHOL width)
    (body : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (ih : (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
        (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
        (v1 : PanSemResultExact width),
      @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) condition = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ state.clock ≠ 0 ∧
        (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState state.decClockHOLFinite body ∧
        res = some v1 ∧ v1 = .continue →
      unchangedLocalGoal name (.while condition body) s1) ∧
    (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
        (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
      @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) condition = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ state.clock ≠ 0 ∧
        (res, s1) = PanSemStateFiniteExact.evaluateHOLFiniteState state.decClockHOLFinite body ∧
        res = none →
      unchangedLocalGoal name (.while condition body) s1) ∧
    (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width),
      @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) condition = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ state.clock ≠ 0 →
      unchangedLocalGoal name body state.decClockHOLFinite)) :
    ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL (.while condition body) ∧
      evaluateHOLFiniteState state (.while condition body) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error →
      post.locals.lookup name = state.locals.lookup name := by
  classical
  intro result post ⟨hfresh, heval, hgood, herror⟩
  have hf : name ∉ freeVarIdsHOL body := by
    intro hmem
    apply hfresh
    simp [freeVarIdsHOL, hmem]
  rw [evaluateHOLFiniteState_while_fixClockRewrite] at heval
  cases hg : @evalHOLExact width σ _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) condition with
  | none =>
      simp only [evalHOLFinite, hg] at heval
      exact False.elim (herror (Prod.mk.inj heval).1.symm)
  | some value =>
      cases value with
      | rStruct fields =>
          simp only [evalHOLFinite, hg] at heval
          exact False.elim (herror (Prod.mk.inj heval).1.symm)
      | nStruct structName fields =>
          simp only [evalHOLFinite, hg] at heval
          exact False.elim (herror (Prod.mk.inj heval).1.symm)
      | val payload =>
          cases payload with
          | word word =>
            by_cases hz : word = 0
            · simp only [evalHOLFinite, hg, hz, ne_eq, not_true_eq_false, ↓reduceIte] at heval
              exact congrArg (fun s => s.locals.lookup name) (Prod.mk.inj heval).2.symm
            · by_cases hc : state.clock = 0
              · simp only [evalHOLFinite, hg, hz, hc, ne_eq, not_false_eq_true, ↓reduceIte] at heval
                simp [← (Prod.mk.inj heval).1, goodResHOL] at hgood
              · have hex : ∃ r st, evaluateHOLFiniteState state.decClockHOLFinite body = (r, st) := ⟨_, _, rfl⟩
                obtain ⟨r, st, hb⟩ := hex
                simp only [evalHOLFinite, hg, hz, hc, ne_eq, not_false_eq_true, ↓reduceIte, hb] at heval
                have hbody := ih.2.2 (.val (.word word)) (.word word) word ⟨hg, rfl, rfl, hz, hc⟩
                cases r with
                | none =>
                    have hmid := hbody none st ⟨hf, hb, rfl, by simp⟩
                    exact (ih.2.1 (.val (.word word)) (.word word) word none st
                      ⟨hg, rfl, rfl, hz, hc, hb.symm, rfl⟩ result post
                      ⟨hfresh, heval, hgood, herror⟩).trans hmid
                | some r =>
                    cases r with
                    | «continue» =>
                        have hmid := hbody (some .continue) st ⟨hf, hb, rfl, by simp⟩
                        exact (ih.1 (.val (.word word)) (.word word) word (some .continue) st .continue
                          ⟨hg, rfl, rfl, hz, hc, hb.symm, rfl, rfl⟩ result post
                          ⟨hfresh, heval, hgood, herror⟩).trans hmid
                    | «break» =>
                        have hmid := hbody (some .break) st ⟨hf, hb, rfl, by simp⟩
                        exact (congrArg (fun s => s.locals.lookup name) (Prod.mk.inj heval).2.symm).trans hmid
                    | error => exact False.elim (herror (Prod.mk.inj heval).1.symm)
                    | timeOut => simp [← (Prod.mk.inj heval).1, goodResHOL] at hgood
                    | returned v => simp [← (Prod.mk.inj heval).1, goodResHOL] at hgood
                    | exception n v => simp [← (Prod.mk.inj heval).1, goodResHOL] at hgood
                    | finalFfi e => simp [← (Prod.mk.inj heval).1, goodResHOL] at hgood

end Flapjack.PanGlobalsUnchangedLocalWhile
