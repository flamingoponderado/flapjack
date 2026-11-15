module

public import Flapjack.Misc.Option.MapM
public import Flapjack.Compiler.Backend.ClosTicks.Source
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Total
public import Mathlib.Tactic

@[expose] public section

/-! Agreement of executable tick removal with the source-shaped traversal. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open ClosLang

theorem removeList_eq_map (expressions : List Exp) :
    removeList expressions = expressions.map removeSing := by
  induction expressions with
  | nil => rfl
  | cons first rest ih => simp [removeList, ih]

/-- Every successful bounded traversal returns the source traversal. -/
theorem removeFuel_eq_source (fuel : Nat) (expression result : Exp)
    (run : removeFuel fuel expression = some result) : result = removeSing expression := by
  induction fuel generalizing expression result with
  | zero => simp [removeFuel] at run
  | succ fuel ih =>
    cases expression
    all_goals simp only [removeFuel] at run
    all_goals simp only [removeSing]
    all_goals try (simp only [bind, Option.bind] at run)
    all_goals repeat' split at run
    all_goals try simp_all [removeList_eq_map, removeFuns_eq_map]
    all_goals aesop (add safe apply mapM_eq_map)

/-- The production retry returns the source traversal for every fuel value. -/
theorem removeBounded_eq_source (fuel : Nat) (expression : Exp) :
    removeBounded fuel expression = some (removeSing expression) := by
  unfold removeBounded
  cases first : removeFuel fuel expression with
  | some value =>
    have equal := removeFuel_eq_source fuel expression value first
    simp [equal]
  | none =>
    have enough : expBudget expression < max fuel (expBudget expression + 1) := by omega
    obtain ⟨result, retry⟩ := removeFuel_succeeds (max fuel (expBudget expression + 1)) expression enough
    have equal := removeFuel_eq_source _ expression result retry
    simpa [first, equal] using retry

end Flapjack.Compiler.Backend.ClosTicks
