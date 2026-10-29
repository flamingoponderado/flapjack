import Flapjack.Compiler.Backend.FlatToClos.Proofs.Thunk
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Force-thunk prerequisites for the flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The generated flat call to a bound thunk payload compiles to the unit
application used by closure thunk forcing. -/
theorem compile_force_application (name : MlString) :
    compile [some name] [FlatSem.appUnit (.varLocal .none name)] =
      [ClosSem.appUnit (.var .none 0)] := by
  simp [compile, compileExps, compileExp, FlatSem.appUnit, ClosSem.appUnit,
    compileOp, arg2, smartCons, nameIndex]

/-- Binding related thunk payloads produces the related one-variable
environments used by the generated force application. -/
theorem force_environment (name : MlString) (source : FlatSem.Value) (target : ClosSem.Value)
    (related : ValueRel source target) :
    EnvRel ⟨[(name, source)]⟩ [some name] [target] := by
  apply (envRel_iff_lookup _ _ _).2
  intro key value found
  by_cases same : key = name
  · subst key
    simp at found
    subst value
    exact ⟨target, by simp [nameIndex], related⟩
  · have different : (key == name) = false := by simp [same]
    simp [List.lookup_cons, different] at found

/-- Simulate force-thunk after its arguments, using the induction hypothesis
for the generated unit application when the thunk is unevaluated. -/
theorem evaluate_force {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (bodySim : ∀ (sourceValue : FlatSem.Value) (targetValue : ClosSem.Value)
        (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      ValueRel sourceValue targetValue → StateRel next nextTarget → next.clock ≤ source.clock →
      (FlatSem.evaluate ⟨[(ofString "f", sourceValue)]⟩ next
        [FlatSem.appUnit (.varLocal .none (ofString "f"))]).2 ≠ .err (.abort .typeError) →
      EvalSim ⟨[(ofString "f", sourceValue)]⟩ [some (ofString "f")] [targetValue] next nextTarget
        [FlatSem.appUnit (.varLocal .none (ofString "f"))])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.thunkOp .forceThunk)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.thunkOp .forceThunk)) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate, flatFix]
    simp only [failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps_reverse] at argsSim
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  rw [FlatSem.evaluate, flatFix] at notTypeError ⊢
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  cases flatArgs : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closArgs : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatArgs, closArgs] at argsSim notTypeError ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have inspection := destThunk_list_related sourceArgs targetArgs next.refs nextTarget.refs related states.2.2.2.1
        cases sourceThunk : FlatSem.destThunk sourceArgs next.refs with
        | badRef => simp [sourceThunk] at notTypeError
        | notThunk => simp [sourceThunk] at notTypeError
        | isThunk mode sourceValue =>
          rw [sourceThunk] at inspection
          generalize targetThunk : ClosSem.destThunk targetArgs nextTarget.refs = outcome at inspection ⊢
          cases inspection with
          | isThunk payloadRel =>
            rename_i targetValue
            cases mode with
            | evaluated =>
              simp [sourceThunk, targetThunk]
              exact ⟨states, .value (.cons payloadRel .nil)⟩
            | notEvaluated =>
                simp [sourceThunk, targetThunk] at notTypeError ⊢
                have generatedNot : (FlatSem.evaluate ⟨[(ofString "f", sourceValue)]⟩ next
                    [FlatSem.appUnit (.varLocal .none (ofString "f"))]).2 ≠ .err (.abort .typeError) := by
                  intro bad
                  simp [bad] at notTypeError
                have bound := FlatSem.evaluate_clock_spec.1 env source next args.reverse _ flatArgs
                have generated := bodySim sourceValue targetValue next nextTarget payloadRel states bound generatedNot
                simp only [EvalSim, compile_force_application] at generated
                cases flatBody : FlatSem.evaluate ⟨[(ofString "f", sourceValue)]⟩ next
                    [FlatSem.appUnit (.varLocal .none (ofString "f"))] with
                | mk after flatResult =>
                  cases closBody : ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [targetValue] nextTarget with
                  | mk closResult afterTarget =>
                    simp only [flatBody, closBody] at generated notTypeError ⊢
                    rcases generated with ⟨bodyStates, bodyResults⟩
                    cases bodyResults with
                    | abort error => exact ⟨bodyStates, .abort error⟩
                    | raise related => exact ⟨bodyStates, .raise related⟩
                    | value relatedValues =>
                      rename_i sourceResults targetResults
                      cases update : FlatSem.updateThunk sourceArgs after.refs sourceResults with
                      | none => simp [update] at notTypeError
                      | some updated =>
                        obtain ⟨targetUpdated, targetUpdate, updatedStates⟩ :=
                          stateRel_updateThunk after afterTarget sourceArgs targetArgs sourceResults targetResults updated
                            bodyStates related relatedValues update
                        simp [update, targetUpdate] at ⊢
                        exact ⟨updatedStates, .value relatedValues⟩

end Flapjack.Compiler.Backend.FlatToClos
