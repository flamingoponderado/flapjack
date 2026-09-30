import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.CallEntry
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermDecCallSupport
/-- Canonical representation roundtrip infrastructure, with no independent HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermDecCallSupport

/-- Original evaluate_fperm DecCall case: the callee IH is guarded by successful
source arguments/code lookup and nonzero clock; the continuation IH additionally
requires the actual returned value and both source shape equalities. These are
recursive evaluation guards, not restrictions on the constructor's conclusion:
all error, timeout, exceptional and normal outcomes are transported. The total
pair evaluator uses the accepted fix_clock erasure, and restores the original
result-name local after the continuation. Full recursive assembly remains open. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_DecCall {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (name : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (state : PanSemStateFiniteExact width σ)
    (ihBody : ∀ values body callee returnShape,
      evalListHOLFinite state
          (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values ∧
      lookupCodeHOLFinite state.code.lookup function values = some (body, callee, returnShape) ∧
      state.clock ≠ 0 →
      ∀ result post,
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result, post) →
      evaluateHOLFiniteState
        { callEntryStateHOLFinite state callee with
          code := fpermCodeHOL f g (callEntryStateHOLFinite state callee).code }
        (fpermHOL f g body) = (result, { post with code := fpermCodeHOL f g post.code }))
    (ihContinuation : ∀ values body callee returnShape value output,
      evalListHOLFinite state
          (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values ∧
      lookupCodeHOLFinite state.code.lookup function values = some (body, callee, returnShape) ∧
      state.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
        (some (.returned value), output) ∧
      shapeOfHOLExact value = shape ∧ shapeOfHOLExact value = returnShape →
      ∀ result post,
      evaluateHOLFiniteState (setVarHOLFinite name value { output with locals := state.locals })
        continuation = (result, post) →
      evaluateHOLFiniteState
        { setVarHOLFinite name value { output with locals := state.locals } with
          code := fpermCodeHOL f g output.code }
        (fpermHOL f g continuation) = (result, { post with code := fpermCodeHOL f g post.code }))
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.decCall name shape function arguments continuation) =
      (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.decCall name shape function arguments continuation)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at heval
  rw [fpermHOL, evaluateHOLFiniteState_decCall_fixClockRewrite]
  rw [FpermCallEntry.arguments f g state arguments]
  cases ha : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none =>
      simp only [ha] at heval ⊢
      cases heval
      rfl
  | some values =>
      simp only [ha] at heval ⊢
      rw [FpermCallEntry.lookup f g state.code function values]
      cases hl : lookupCodeHOLFinite state.code.lookup function values with
      | none =>
          simp only [hl, Option.map_none] at heval ⊢
          cases heval
          rfl
      | some triple =>
          obtain ⟨body, callee, returnShape⟩ := triple
          simp only [hl, Option.map_some] at heval ⊢
          by_cases hc : state.clock = 0
          · simp only [hc, if_true] at heval ⊢
            cases heval
            simp only [emptyLocalsHOLFinite, hc]
          · simp only [hc, if_false] at heval ⊢
            rw [FpermCallEntry.entry]
            rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
              ⟨br, output⟩
            have ht := ihBody values body callee returnShape ⟨ha, hl, hc⟩ br output hb
            simp only [callEntryStateHOLFinite] at ht
            simp only [callEntryStateHOLFinite]
            rw [ht]
            simp only [hb] at heval
            cases br with
            | none =>
                cases heval
                rfl
            | some result =>
                cases result with
                | returned value =>
                    by_cases hg : (shapeEqHOL (shapeOfHOLExact value) shape &&
                      shapeEqHOL (shapeOfHOLExact value) returnShape) = true
                    · simp only [hg, if_true] at heval ⊢
                      have hs : shapeOfHOLExact value = shape ∧
                          shapeOfHOLExact value = returnShape := by
                        simpa only [Bool.and_eq_true, shapeEqHOL_eq_true] using hg
                      rcases hk : evaluateHOLFiniteState
                          (setVarHOLFinite name value { output with locals := state.locals })
                          continuation with ⟨rr, final⟩
                      have hcont := ihContinuation values body callee returnShape value output
                        ⟨ha, hl, hc, hb, hs⟩ rr final hk
                      simp only [setVarHOLFinite] at hcont
                      simp only [setVarHOLFinite]
                      rw [hcont]
                      simp only [hk] at heval ⊢
                      cases heval
                      rfl
                    · simp only [hg] at heval ⊢
                      cases heval
                      rfl
                | «break» | «continue» | error | timeOut | exception | finalFfi =>
                    cases heval
                    rfl

end Flapjack
