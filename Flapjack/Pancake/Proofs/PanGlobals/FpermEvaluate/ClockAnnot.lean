import Flapjack.Pancake.Proofs.PanGlobals.FpermCode

/-! Tick and Annot cases of pan_globalsProofScript's evaluate_fperm (1721-1810).
These retain the original premise and conclusion for clock/annotation leaves;
no code lookup or recursive induction premise is needed for these cases.
The evaluator returns the original total result/state pair. -/

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermClockAnnotSupport
/-- Representation infrastructure, with no independent HOL declaration:
re-export the canonical state's genuine toExact/ofExact roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermClockAnnotSupport

/-- Original evaluate_fperm specialized to Annot. HOL fperm's identity
clause preserves the constructor, and evaluate_def preserves the whole state.
The four canonical state maps and positive word carrier are explicitly qualified. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Annot {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ) (tag text : MlS)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.annot tag text : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.annot tag text : ProgHOL width)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  rw [evaluateHOLFiniteState_annot] at heval
  have hpost : state = post := congrArg Prod.snd heval
  have hres : (none : Option (PanSemResultExact width)) = res := congrArg Prod.fst heval
  cases hpost
  cases hres
  rw [fpermHOL]
  · exact evaluateHOLFiniteState_annot { state with code := fpermCodeHOL f g state.code } tag text
  all_goals simp

/-- Original evaluate_fperm specialized to Tick. HOL fperm's identity
clause preserves the constructor; timeout and decrement branches remain explicit.
The four canonical state maps and positive word carrier are explicitly qualified. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Tick {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.tick : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.tick : ProgHOL width)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  rw [fpermHOL]
  · rw [evaluateHOLFiniteState_tick] at heval ⊢
    by_cases hc : state.clock = 0
    · simp only [if_pos hc, emptyLocalsHOLFinite] at heval ⊢
      simpa only [Prod.fst, Prod.snd] using congrArg
        (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
          (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
    · simp only [if_neg hc, decClockHOLFinite] at heval ⊢
      simpa only [Prod.fst, Prod.snd] using congrArg
        (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
          (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
  all_goals simp

end Flapjack
