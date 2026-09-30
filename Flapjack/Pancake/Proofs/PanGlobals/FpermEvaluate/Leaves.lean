import Flapjack.Pancake.Proofs.PanGlobals.FpermCode

/-! Atomic cases of pan_globalsProofScript's evaluate_fperm (1721-1810).
These specialize the original premise and conclusion to the three atoms;
no code lookup or recursive induction premise is needed for these cases.
The evaluator returns the original total result/state pair. -/

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermEvaluateSupport
/-- Representation infrastructure, with no independent HOL declaration:
re-export the canonical state's genuine toExact/ofExact roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermEvaluateSupport

/-- Original evaluate_fperm specialized to Skip. HOL fperm's identity
clause preserves the constructor, and evaluate_def preserves the whole state.
The four canonical state maps and positive word carrier are explicitly qualified. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Skip {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.skip : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.skip : ProgHOL width)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  rw [evaluateHOLFiniteState_skip] at heval
  have hpost : state = post := congrArg Prod.snd heval
  have hres : (none : Option (PanSemResultExact width)) = res := congrArg Prod.fst heval
  cases hpost
  cases hres
  rw [fpermHOL]
  · exact evaluateHOLFiniteState_skip { state with code := fpermCodeHOL f g state.code }
  all_goals simp

/-- Original evaluate_fperm specialized to Break. HOL fperm's identity
clause preserves the constructor, and evaluate_def preserves the whole state.
The four canonical state maps and positive word carrier are explicitly qualified. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Break {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.break : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.break : ProgHOL width)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  rw [evaluateHOLFiniteState_break] at heval
  have hpost : state = post := congrArg Prod.snd heval
  have hres : (some .break : Option (PanSemResultExact width)) = res := congrArg Prod.fst heval
  cases hpost
  cases hres
  rw [fpermHOL]
  · exact evaluateHOLFiniteState_break { state with code := fpermCodeHOL f g state.code }
  all_goals simp

/-- Original evaluate_fperm specialized to Continue. HOL fperm's identity
clause preserves the constructor, and evaluate_def preserves the whole state.
The four canonical state maps and positive word carrier are explicitly qualified. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Continue {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.continue : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.continue : ProgHOL width)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  rw [evaluateHOLFiniteState_continue] at heval
  have hpost : state = post := congrArg Prod.snd heval
  have hres : (some .continue : Option (PanSemResultExact width)) = res := congrArg Prod.fst heval
  cases hpost
  cases hres
  rw [fpermHOL]
  · exact evaluateHOLFiniteState_continue { state with code := fpermCodeHOL f g state.code }
  all_goals simp

end Flapjack
