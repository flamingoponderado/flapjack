import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

/-! Return and Raise cases of pan_globalsProofScript's evaluate_fperm.
Expression evaluation is unchanged by code updates. The original value-size,
exception-shape and failure clauses remain explicit in the total evaluator.
-/
namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact
namespace FpermReturnRaiseSupport
/-- Canonical representation infrastructure, not an independently named HOL theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermReturnRaiseSupport

/-- Original evaluate_fperm Return case with the original source evaluation
premise and full code-permuted target/post-state equality. Every evaluator
failure and contextual-size branch is retained; the shape guard in Raise is
also retained. Classical memory deciders are internal to the total evaluator. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Return {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (expression : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.return expression : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.return expression : ProgHOL width)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  have he : @evalHOLExact width σ _
      ({ state with code := fpermCodeHOL f g state.code } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (fpermCodeHOL f g state.code)) expression
  rw [fpermHOL]
  · rw [evaluateHOLFiniteState_return] at heval ⊢
    rw [he]
    cases hv : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression with
    | none =>
        simp only [hv] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
    | some value =>
        by_cases hs : sizeOfShapeWithContextHOL state.structs (shapeOfHOLExact value) ≤ 32
        · simp only [hv, if_pos hs] at heval ⊢
          simpa only [Prod.fst, Prod.snd, emptyLocalsHOLFinite] using congrArg
            (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
              (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
        · simp only [hv, if_neg hs] at heval ⊢
          simpa only [Prod.fst, Prod.snd] using congrArg
            (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
              (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
  all_goals simp

/-- Original evaluate_fperm Raise case with the original source evaluation
premise and full code-permuted target/post-state equality. Every evaluator
failure and contextual-size branch is retained; the shape guard in Raise is
also retained. Classical memory deciders are internal to the total evaluator. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Raise {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (exceptionId : MlS)
    (expression : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.raise exceptionId expression : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.raise exceptionId expression : ProgHOL width)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  have he : @evalHOLExact width σ _
      ({ state with code := fpermCodeHOL f g state.code } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (fpermCodeHOL f g state.code)) expression
  rw [fpermHOL]
  · rw [evaluateHOLFiniteState_raise] at heval ⊢
    rw [he]
    cases hshape : state.eshapes.lookup exceptionId with
    | none =>
        simp only [hshape] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
    | some shape =>
        cases hv : @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) expression with
        | none =>
            simp only [hshape, hv] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
        | some value =>
            by_cases hc : shapeOfHOLExact value = shape ∧
              sizeOfShapeWithContextHOL state.structs (shapeOfHOLExact value) ≤ 32
            · simp only [hshape, hv, if_pos hc] at heval ⊢
              simpa only [Prod.fst, Prod.snd, emptyLocalsHOLFinite] using congrArg
                (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                  (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
            · simp only [hshape, hv, if_neg hc] at heval ⊢
              simpa only [Prod.fst, Prod.snd] using congrArg
                (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                  (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
  all_goals simp

end Flapjack
