import Flapjack.Compiler.Backend.BvlHandle.Helpers
import Flapjack.Compiler.Backend.BvlHandle.Proofs.HelpersTotal
import Aesop

/-! Source and production correspondence for handler-pass helpers. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl BvlToBvi

private theorem canRaiseList_eq_any (xs : List Exp) : canRaiseList xs = xs.any canRaise := by
  induction xs with
  | nil => simp [canRaiseList]
  | cons e es ih => simp [canRaiseList, ih]

private theorem foldRaise_eq (visit : Exp → Option Bool)
    (correct : ∀ e b, visit e = some b → b = canRaise e)
    (xs : List Exp) (init result : Bool)
    (run : xs.foldlM (fun b x => if b then pure true else visit x) init = some result) :
    result = (init || xs.any canRaise) := by
  induction xs generalizing init with
  | nil => simpa using run.symm
  | cons e es ih =>
    cases init with
    | true =>
      simp only [List.foldlM_cons] at run
      have h := ih true run
      simpa using h
    | false =>
      simp only [List.foldlM_cons, Bool.false_eq_true, ↓reduceIte] at run
      cases visitRun : visit e with
      | none => simp [visitRun] at run
      | some value =>
        simp only [visitRun, bind, Option.bind] at run
        have eq := correct e value visitRun
        have h := ih value run
        simpa [eq, Bool.or_assoc] using h

/-- Any successful fuel-bounded raise test equals the source test. -/
theorem canRaiseFuel_eq (fuel : Nat) (expression : Exp) (result : Bool)
    (run : canRaiseFuel fuel expression = some result) : result = canRaise expression := by
  induction fuel generalizing expression result with
  | zero => simp [canRaiseFuel] at run
  | succ fuel ih =>
    cases expression with
    | var n => simpa [canRaiseFuel, canRaise] using run.symm
    | force a b => simpa [canRaiseFuel, canRaise] using run.symm
    | raise body => simpa [canRaiseFuel, canRaise] using run.symm
    | call ticks dest args => simpa [canRaiseFuel, canRaise] using run.symm
    | tick body =>
      simp only [canRaiseFuel] at run
      simpa [canRaise] using ih body result run
    | handle body handler =>
      simp only [canRaiseFuel] at run
      simpa [canRaise] using ih handler result run
    | ifThenElse x y z =>
      have h := foldRaise_eq (canRaiseFuel fuel) ih [x, y, z] false result run
      simpa [canRaise, Bool.or_assoc] using h
    | «let» xs body =>
      have h := foldRaise_eq (canRaiseFuel fuel) ih (body :: xs) false result run
      simpa [canRaise, canRaiseList_eq_any] using h
    | op op xs =>
      cases op with
      | thunkOp operation =>
        cases operation <;> simp only [canRaiseFuel] at run <;> simp only [canRaise]
        all_goals try (simpa using run.symm)
        all_goals have h := foldRaise_eq (canRaiseFuel fuel) ih xs false result run
        all_goals simpa [canRaiseList_eq_any] using h
      | _ =>
        have h := foldRaise_eq (canRaiseFuel fuel) ih xs false result run
        simpa [canRaise, canRaiseList_eq_any] using h

/-- The executed bounded raise test always returns the source result. -/
theorem canRaiseBounded_eq (fuel : Nat) (expression : Exp) :
    canRaiseBounded fuel expression = some (canRaise expression) := by
  cases first : canRaiseFuel fuel expression with
  | some result =>
    have correct := canRaiseFuel_eq fuel expression result first
    simp [canRaiseBounded, first, correct]
  | none =>
    have bound : expBudget expression < max fuel (expBudget expression + 1) := by omega
    obtain ⟨result, run⟩ := canRaiseFuel_succeeds _ expression bound
    have correct := canRaiseFuel_eq _ expression result run
    simp [canRaiseBounded, first, run, correct]

/-- The source list adjustment is a map of its single-expression adjustment. -/
theorem handleAdjVarsList_eq_map (depth shift : Nat) (xs : List Exp) :
    handleAdjVarsList depth shift xs = xs.map (handleAdjVars depth shift) := by
  induction xs with
  | nil => simp [handleAdjVarsList]
  | cons x xs ih => simp [handleAdjVarsList, ih]

private theorem mapM_eq_map {α β : Type} (visit : α → Option β) (f : α → β)
    (correct : ∀ x y, visit x = some y → y = f x) (xs : List α) (ys : List β)
    (run : xs.mapM visit = some ys) : ys = xs.map f := by
  induction xs generalizing ys with
  | nil => simpa using run.symm
  | cons x rest ih =>
    simp only [List.mapM_cons] at run
    cases first : visit x with
    | none => simp [first] at run
    | some value =>
      cases remaining : rest.mapM visit with
      | none => simp [first, remaining] at run
      | some values =>
        simp [first, remaining] at run
        subst ys
        simp [correct x value first, ih values remaining]

/-- Every successful bounded variable adjustment agrees with HOL. -/
theorem adjustVarsFuel_eq (fuel depth shift : Nat) (expression result : Exp)
    (run : adjustVarsFuel fuel depth shift expression = some result) :
    result = handleAdjVars depth shift expression := by
  induction fuel generalizing depth shift expression result with
  | zero => simp [adjustVarsFuel] at run
  | succ fuel ih =>
    cases expression <;> simp only [adjustVarsFuel] at run <;>
      try simp only [handleAdjVars]
    all_goals try (simp only [bind, Option.bind] at run)
    all_goals repeat' split at run
    all_goals try simp_all [handleAdjVarsList_eq_map, Nat.not_lt]
    all_goals aesop (add safe apply mapM_eq_map) (add safe forward Nat.not_lt_of_ge)

/-- The executed bounded adjustment always returns the source result. -/
theorem adjustVarsBounded_eq (fuel depth shift : Nat) (expression : Exp) :
    adjustVarsBounded fuel depth shift expression = some (handleAdjVars depth shift expression) := by
  cases first : adjustVarsFuel fuel depth shift expression with
  | some result =>
    have correct := adjustVarsFuel_eq fuel depth shift expression result first
    simp [adjustVarsBounded, first, correct]
  | none =>
    have bound : expBudget expression < max fuel (expBudget expression + 1) := by omega
    obtain ⟨result, run⟩ := adjustVarsFuel_succeeds _ depth shift expression bound
    have correct := adjustVarsFuel_eq _ depth shift expression result run
    simp [adjustVarsBounded, first, run, correct]

end Flapjack.Compiler.Backend.BvlHandle
