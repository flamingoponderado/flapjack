import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

/-! Primitive case of pan_globalsProofScript's evaluate_fperm.
Expression evaluation and keyed-variable validity are unchanged by code updates.
List, operator and local validity failure clauses remain explicit.
-/
namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact
namespace FpermPrimitiveSupport
/-- Canonical representation infrastructure, not an independently named HOL theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermPrimitiveSupport

/-- Original evaluate_fperm Primitive case. The sole original source-run premise
and full target/post-state equality retain expression failure and validity
branches, including list and operator failure. The local write commutes with code update. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Primitive {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL width))
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.primitive name operator arguments : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.primitive name operator arguments : ProgHOL width)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLExact width σ _
      ({ state with code := fpermCodeHOL f g state.code } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (fpermCodeHOL f g state.code)) expression
  have he : @evalListHOLExact width σ _
      ({ state with code := fpermCodeHOL f g state.code } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      @evalListHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) arguments := by
    clear heval
    induction arguments with
    | nil => rfl
    | cons expression rest ih =>
        simp only [evalListHOLExact, ih]
        rw [point]
  have hvalid (value : ValueHOL width) :
      isValidValueHOLFinite { state with code := fpermCodeHOL f g state.code } .local name value =
        isValidValueHOLFinite state .local name value := rfl
  have hset (value : ValueHOL width) :
      setVarHOLFinite name value { state with code := fpermCodeHOL f g state.code } =
        { setVarHOLFinite name value state with
          code := fpermCodeHOL f g (setVarHOLFinite name value state).code } := rfl
  rw [fpermHOL]
  · rw [evaluateHOLFiniteState_primitive] at heval ⊢
    rw [he]
    cases hv : @evalListHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    | none =>
        simp only [hv] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
    | some values =>
        simp only [hv] at heval ⊢
        cases hp : panPrimopHOLExact operator values with
        | none =>
            simp only [hp] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
        | some value =>
            simp only [hp] at heval ⊢
            rw [hvalid]
            by_cases hs : isValidValueHOLFinite state .local name value = true
            · simp only [hs, if_true] at heval ⊢
              rw [hset]
              simpa only [Prod.fst, Prod.snd] using congrArg
                (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                  (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
            · simp only [if_neg hs] at heval ⊢
              simpa only [Prod.fst, Prod.snd] using congrArg
                (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                  (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
  all_goals simp

end Flapjack
