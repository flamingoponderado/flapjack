import Flapjack.Compiler.Backend.ClosCall.Proofs.PrimitiveWellformed
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

/-! Well-formedness of thunk inspection and updates. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

/-- Inspecting a thunk in a well-formed reference store yields a
well-formed payload. -/
theorem destThunk_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (targets : List Value)
    (state : ClosSem.State C F) (mode : Flapjack.AstHOL.ThunkMode) (value : Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (run : destThunk targets state.refs = .isThunk mode value) :
    ValueWellFormedFuel fuel g allowed code value := by
  unfold destThunk at run
  repeat' split at run
  all_goals simp_all
  all_goals exact stateWf.2.1 _ _ (by assumption)

/-- Successful memoization stores a well-formed result in the thunk and
preserves the source-state invariant. -/
theorem updateThunk_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (targets values : List Value)
    (state : ClosSem.State C F) (refs : HolFiniteMapExact Nat (Ref Value))
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (valuesWf : ValuesWellFormedFuel fuel g allowed code values)
    (run : updateThunk targets state.refs values = some refs) :
    StateWellFormedFuel fuel g allowed code { state with refs := refs } := by
  unfold updateThunk at run
  repeat' split at run
  all_goals simp_all [storeThunk]
  all_goals repeat' split at run
  all_goals simp_all
  all_goals subst refs
  all_goals apply stateWellFormedFuel_updateRef stateWf
  all_goals exact valuesWellFormedFuel_mem valuesWf (by simp)

/-- An evaluation outcome has well-formed values and a well-formed state. -/
def EvalWellFormedFuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (outcome : ClosSem.EvalResult C F) : Prop :=
  ResultWellFormedFuel fuel g allowed code outcome.1 ∧ StateWellFormedFuel fuel g allowed code outcome.2

/-- The evaluator's force-thunk case preserves the invariant assuming the
argument and forced-body induction hypotheses. -/
theorem evaluate_force_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state : ClosSem.State C F)
    (argsIH : EvalWellFormedFuel fuel g allowed code (evaluate args env state))
    (bodyIH : ∀ (value : Value) (start : ClosSem.State C F), start.clock ≤ state.clock →
      ValueWellFormedFuel fuel g allowed code value →
      StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [appUnit (.var .none 0)] [value] start)) :
    EvalWellFormedFuel fuel g allowed code
      (evaluate [.op trace (.thunkOp .forceThunk) args] env state) := by
  cases argsRun : evaluate args env state with
  | mk argsResult argsFinal =>
    rw [argsRun] at argsIH
    rw [evaluate, fixClock_evaluate, argsRun]
    cases argsResult with
    | err error => simpa [EvalWellFormedFuel] using argsIH
    | val targets =>
      cases inspected : destThunk targets argsFinal.refs with
      | badRef => simpa [EvalWellFormedFuel, ResultWellFormedFuel, inspected] using argsIH.2
      | notThunk => simpa [EvalWellFormedFuel, ResultWellFormedFuel, inspected] using argsIH.2
      | isThunk mode value =>
        have valueWf := destThunk_wellFormedFuel targets argsFinal mode value argsIH.2 inspected
        cases mode with
        | evaluated =>
          simpa [EvalWellFormedFuel, ResultWellFormedFuel, inspected] using
            And.intro (ValuesWellFormedFuel.cons valueWf .nil) argsIH.2
        | notEvaluated =>
          have argsBound := evaluate_clock_le args env state
          rw [argsRun] at argsBound
          have bodyWf := bodyIH value argsFinal argsBound valueWf argsIH.2
          cases bodyRun : evaluate [appUnit (.var .none 0)] [value] argsFinal with
          | mk bodyResult bodyFinal =>
            rw [bodyRun] at bodyWf
            cases bodyResult with
            | err error => simpa [EvalWellFormedFuel, inspected, bodyRun] using bodyWf
            | val forced =>
              cases stored : updateThunk targets bodyFinal.refs forced with
              | none => simpa [EvalWellFormedFuel, ResultWellFormedFuel, inspected, bodyRun, stored] using bodyWf.2
              | some refs =>
                simpa [EvalWellFormedFuel, ResultWellFormedFuel, inspected, bodyRun, stored] using
                  And.intro bodyWf.1 (updateThunk_wellFormedFuel targets forced bodyFinal refs bodyWf.2 bodyWf.1 stored)

end Flapjack.Compiler.Backend.ClosCall
