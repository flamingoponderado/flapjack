import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

/-! Assign case of pan_globalsProofScript's evaluate_fperm.
Expression evaluation and keyed-variable validity are unchanged by code updates.
Both variable kinds and the original failure clauses remain explicit.
-/
namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact
namespace FpermAssignSupport
/-- Canonical representation infrastructure, not an independently named HOL theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermAssignSupport

/-- Original evaluate_fperm Assign case. The sole original source-run premise
and full target/post-state equality retain expression failure and validity
branches. Local/global writes commute with code update by their original fields. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Assign {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (kind : VarKind) (name : MlS) (expression : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.assign kind name expression : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.assign kind name expression : ProgHOL width)) =
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
  have hvalid (value : ValueHOL width) :
      isValidValueHOLFinite { state with code := fpermCodeHOL f g state.code } kind name value =
        isValidValueHOLFinite state kind name value := by
    cases kind <;> rfl
  have hset (value : ValueHOL width) :
      setKvarHOLFinite kind name value { state with code := fpermCodeHOL f g state.code } =
        { setKvarHOLFinite kind name value state with
          code := fpermCodeHOL f g (setKvarHOLFinite kind name value state).code } := by
    cases kind <;> rfl
  rw [fpermHOL]
  · rw [evaluateHOLFiniteState_assign] at heval ⊢
    rw [he]
    cases hv : @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) expression with
    | none =>
        simp only [hv] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
    | some value =>
        simp only [hv] at heval ⊢
        rw [hvalid]
        by_cases hs : isValidValueHOLFinite state kind name value = true
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
