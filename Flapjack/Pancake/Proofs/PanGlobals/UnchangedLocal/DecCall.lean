import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsUnchangedLocalDecCall
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export; no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Original unchanged-local DecCall case. The unused value binder is retained;
    the sole continuation IH has all original evaluate_ind source guards. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_DecCall {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (bound : MlS) (shape : ShapeHOL)
    (function : MlS) (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (state : PanSemStateFiniteExact width σ)
    (ih : ∀ args body callee returnShape retv (output : PanSemStateFiniteExact width σ),
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some args ∧
      lookupCodeHOLFinite state.code.lookup function args = some (body,callee,returnShape) ∧
      state.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned retv),output) ∧
      shapeOfHOLExact retv = shape ∧ shapeOfHOLExact retv = returnShape →
      ∀ result (post : PanSemStateFiniteExact width σ),
        name ∉ freeVarIdsHOL continuation ∧
        evaluateHOLFiniteState (setVarHOLFinite bound retv {output with locals := state.locals}) continuation = (result,post) ∧
        goodResHOL result = true ∧ result ≠ some .error →
        post.locals.lookup name = (setVarHOLFinite bound retv {output with locals := state.locals}).locals.lookup name) :
    ∀ result (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL (.decCall bound shape function arguments continuation) ∧
      evaluateHOLFiniteState state (.decCall bound shape function arguments continuation) = (result,post) ∧
      goodResHOL result = true ∧ result ≠ some .error →
      post.locals.lookup name = state.locals.lookup name := by
  classical
  intro result post ⟨hfresh,hev,hgood,herror⟩
  have hn : name ≠ bound := by
    intro heq; subst name; apply hfresh; simp [freeVarIdsHOL]
  have hf : name ∉ freeVarIdsHOL continuation := by
    intro hm; apply hfresh; simp [freeVarIdsHOL,hm]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hev
  cases ha : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => simp only [ha] at hev; exact False.elim (herror (Prod.mk.inj hev).1.symm)
  | some args =>
    simp only [ha] at hev
    cases hl : lookupCodeHOLFinite state.code.lookup function args with
    | none => simp only [hl] at hev; exact False.elim (herror (Prod.mk.inj hev).1.symm)
    | some entry =>
      rcases entry with ⟨body,callee,returnShape⟩
      simp only [hl] at hev
      by_cases hz : state.clock = 0
      · simp only [if_pos hz] at hev
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
        simp [goodResHOL] at hgood
      · simp only [if_neg hz] at hev
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨br,output⟩
        simp only [hb] at hev
        cases br with
        | none => exact False.elim (herror (Prod.mk.inj hev).1.symm)
        | some br =>
          cases br with
          | «break» | «continue» | error => exact False.elim (herror (Prod.mk.inj hev).1.symm)
          | timeOut | exception eid value | finalFfi outcome =>
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
            simp [goodResHOL] at hgood
          | returned retv =>
            by_cases hs : shapeOfHOLExact retv = shape ∧ shapeOfHOLExact retv = returnShape
            · have hg : (shapeEqHOL (shapeOfHOLExact retv) shape && shapeEqHOL (shapeOfHOLExact retv) returnShape) = true := by
                simpa only [Bool.and_eq_true,shapeEqHOL_eq_true] using hs
              simp only [hg,↓reduceIte] at hev
              rcases hc : evaluateHOLFiniteState (setVarHOLFinite bound retv {output with locals := state.locals}) continuation with ⟨cr,cp⟩
              simp only [hc] at hev
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
              have hi := ih args body callee returnShape retv output ⟨ha,hl,hz,hb,hs.1,hs.2⟩ cr cp ⟨hf,hc,hgood,herror⟩
              simp [setVarHOLFinite,FUPDATE,Ne.symm hn] at hi
              rw [lookup_resVarEq_toExact]
              cases state.locals.lookup bound <;> simpa [resVarHOLExact,hn] using hi
            · have hg : (shapeEqHOL (shapeOfHOLExact retv) shape && shapeEqHOL (shapeOfHOLExact retv) returnShape) = false := by
                cases he : (shapeEqHOL (shapeOfHOLExact retv) shape && shapeEqHOL (shapeOfHOLExact retv) returnShape)
                · rfl
                · exact False.elim (hs (by simpa only [Bool.and_eq_true,shapeEqHOL_eq_true] using he))
              simp only [hg] at hev
              exact False.elim (herror (Prod.mk.inj hev).1.symm)

end Flapjack.PanGlobalsUnchangedLocalDecCall
