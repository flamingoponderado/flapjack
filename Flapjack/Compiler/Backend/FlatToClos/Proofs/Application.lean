import Flapjack.Compiler.Backend.FlatToClos.Proofs.Call

/-! Application-expression simulation for the flat-to-closure pass. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Simulate a two-expression unary application using the induction
hypotheses for the argument, function, and selected function body. -/
theorem evaluate_application {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (function argument : FlatLang.Exp)
    (argumentSim : EvalSim env names values source target [argument])
    (functionSim : ∀ (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      StateRel next nextTarget →
      (FlatSem.evaluate env next [function]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values next nextTarget [function])
    (bodySim : ∀ (next : FlatSem.State C F) (nextTarget : ClosSem.State C F)
        (nextEnv : FlatSem.Environment FlatSem.Value) (body : FlatLang.Exp)
        (newNames : List (Option MlString)) (newValues : List ClosSem.Value),
      EnvRel nextEnv newNames newValues → FlatProps.noMat body = true →
      StateRel (FlatSem.decClock next) (ClosSem.decClock 1 nextTarget) →
      (FlatSem.evaluate nextEnv (FlatSem.decClock next) [body]).2 ≠ .err (.abort .typeError) →
      EvalSim nextEnv newNames newValues (FlatSem.decClock next) (ClosSem.decClock 1 nextTarget) [body])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .opapp) [function, argument]]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .opapp) [function, argument]] := by
  unfold EvalSim at argumentSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, arg2, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at argumentSim ⊢
  rw [FlatSem.evaluate] at notTypeError ⊢
  rw [ClosSem.evaluate]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at notTypeError ⊢
  rw [(FlatSem.fixClock_evaluations env source [argument, function] argument []).1] at notTypeError ⊢
  rw [ClosSem.fixClock_evaluate]
  rw [FlatSem.evaluate] at notTypeError ⊢
  rw [(FlatSem.fixClock_evaluations env source [argument] argument []).1] at notTypeError ⊢
  dsimp only at notTypeError ⊢
  cases flatArg : FlatSem.evaluate env source [argument] with
  | mk next argResult =>
    cases closArg : ClosSem.evaluate [compileExp names argument] values target with
    | mk targetArgResult nextTarget =>
      simp only [flatArg, closArg] at argumentSim notTypeError ⊢
      rcases argumentSim with ⟨argStates, argResults⟩
      cases argResults with
      | abort error => exact ⟨argStates, .abort error⟩
      | raise related => exact ⟨argStates, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next argument _ flatArg
        cases related with
        | nil => simp at length
        | cons argRel tail =>
          cases tail with
          | nil =>
            rename_i sourceArg targetArg
            simp at notTypeError ⊢
            have functionNot : (FlatSem.evaluate env next [function]).2 ≠ .err (.abort .typeError) := by
              intro bad
              simp [bad] at notTypeError
            have functionRelated := functionSim next nextTarget argStates functionNot
            simp only [EvalSim, compile, compileExps] at functionRelated
            rw [ClosSem.fixClock_evaluate]
            cases flatFunction : FlatSem.evaluate env next [function] with
            | mk after flatResult =>
              cases closFunction : ClosSem.evaluate [compileExp names function] values nextTarget with
              | mk targetResult afterTarget =>
                simp only [flatFunction, closFunction] at functionRelated notTypeError ⊢
                rcases functionRelated with ⟨funStates, funResults⟩
                cases funResults with
                | abort error => exact ⟨funStates, .abort error⟩
                | raise valueRel => exact ⟨funStates, .raise valueRel⟩
                | value functionRel =>
                  have funLength := FlatSem.evaluate_singleton_length env next after function _ flatFunction
                  cases functionRel with
                  | nil => simp at funLength
                  | cons head rest =>
                    cases rest with
                    | cons _ _ => simp at funLength
                    | nil =>
                      rename_i sourceFunction targetFunction
                      simp at notTypeError ⊢
                      cases applied : FlatSem.doOpApp [sourceFunction, sourceArg] with
                      | none => simp [applied] at notTypeError
                      | some pair =>
                        obtain ⟨nextEnv, body⟩ := pair
                        simp [applied] at notTypeError ⊢
                        exact evaluate_call_related after afterTarget sourceFunction targetFunction sourceArg targetArg
                          nextEnv body funStates head argRel applied (bodySim after afterTarget nextEnv body) notTypeError
          | cons _ _ => simp at length

end Flapjack.Compiler.Backend.FlatToClos
