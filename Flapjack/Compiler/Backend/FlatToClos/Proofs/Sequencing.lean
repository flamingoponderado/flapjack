import Flapjack.Compiler.Backend.FlatToClos.Proofs.FlatOperators

/-! Bounded-clock sequencing for the proof-side evaluator induction. These
lemmas are Flapjack infrastructure, not reviewed HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Singleton simulations at clocks below a bound compose into a list
simulation at that bound. -/
theorem evaluate_list_of_singletons {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (expressions : List FlatLang.Exp) (clockBound : Nat)
    (singletons : ∀ expression, expression ∈ expressions →
      ∀ (source : FlatSem.State C F) (target : ClosSem.State C F),
      source.clock ≤ clockBound → StateRel source target →
      (FlatSem.evaluate env source [expression]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [expression])
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (clockLe : source.clock ≤ clockBound) (states : StateRel source target)
    (notTypeError : (FlatSem.evaluate env source expressions).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target expressions := by
  induction expressions generalizing source target with
  | nil => exact evaluate_nil env names values source target states
  | cons first tail ih =>
    cases tail with
    | nil => exact singletons first (by simp) source target clockLe states notTypeError
    | cons second rest =>
      apply evaluate_cons env names values source target first second rest
      · exact singletons first (by simp) source target clockLe states
      · intro next nextTarget nextStates nextClock nextNot
        apply ih
        · intro expression member
          exact singletons expression (by simp [member])
        · exact le_trans nextClock clockLe
        · exact nextStates
        · exact nextNot
      · exact notTypeError

/-- Singleton simulations below a bound also compose into installed
declaration sequences with their final unit expression. -/
theorem evaluate_decs_unit_of_singletons {C F : Type}
    (declarations : List FlatLang.Exp) (clockBound : Nat)
    (singletons : ∀ expression, expression ∈ declarations →
      ∀ (source : FlatSem.State C F) (target : ClosSem.State C F),
      source.clock ≤ clockBound → StateRel source target →
      (FlatSem.evaluate ⟨[]⟩ source [expression]).2 ≠ .err (.abort .typeError) →
      EvalSim ⟨[]⟩ [] [] source target [expression])
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (clockLe : source.clock ≤ clockBound) (states : StateRel source target)
    (notTypeError : (FlatSem.evaluateDecs source declarations).2 ≠ some (.abort .typeError)) :
    DecUnitSim source target declarations := by
  induction declarations generalizing source target with
  | nil => exact evaluate_decs_unit_nil source target states
  | cons first rest ih =>
    apply evaluate_decs_unit_cons source target first rest
    · exact singletons first (by simp) source target clockLe states
    · intro next nextTarget nextStates nextClock nextNot
      apply ih
      · intro expression member
        exact singletons expression (by simp [member])
      · exact le_trans nextClock clockLe
      · exact nextStates
      · exact nextNot
    · exact notTypeError

end Flapjack.Compiler.Backend.FlatToClos
