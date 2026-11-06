import Flapjack.Compiler.Backend.BviTmc.Proofs.PureTotal

/-! Source-shaped TMC purity and correspondence with the executed traversal. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi

mutual
/-- Source purity test for a single expression. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "pure_exp_def"]
def pureExp (n : Nat) : Exp → Bool
  | .var v => v < n
  | .let xs body => pureExp n body && pureExps n xs
  | .op op xs => pureOp op xs && pureExps n xs
  | _ => false
termination_by e => expBudget e
decreasing_by all_goals simp [expBudget] <;> omega

/-- Source purity test for an expression list. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "pure_exp_def"]
def pureExps (n : Nat) : List Exp → Bool
  | [] => true
  | x :: xs => pureExp n x && pureExps n xs
termination_by xs => listBudget xs
decreasing_by all_goals simp [listBudget] <;> omega
end

private theorem pureExps_eq_all (n : Nat) (xs : List Exp) :
    pureExps n xs = xs.all (pureExp n) := by
  induction xs with
  | nil => simp [pureExps]
  | cons x xs ih => simp [pureExps, ih]

private theorem foldPure_success_eq {α : Type} (xs : List α) (f : α → Option Bool) (g : α → Bool)
    (init result : Bool) (agree : ∀ x value, f x = some value → value = g x)
    (run : xs.foldlM (fun yes x => if yes then f x else pure false) init = some result) :
    result = (init && xs.all g) := by
  induction xs generalizing init result with
  | nil => simpa using (Option.some.inj run).symm
  | cons x xs ih =>
    cases init with
    | false =>
      have equal := ih false result (by simpa using run)
      simpa using equal
    | true =>
      cases hx : f x with
      | none => simp [hx] at run
      | some value =>
        have equal := ih value result (by simpa [hx] using run)
        rw [agree x value hx] at equal
        simpa using equal

/-- Any successful fuel-bounded purity traversal equals the original
structural purity test, including short-circuiting traversals. -/
theorem pureFuel_success_eq (fuel n : Nat) (expression : Exp) (result : Bool)
    (run : pureFuel fuel n expression = some result) : result = pureExp n expression := by
  induction fuel generalizing expression result with
  | zero => simp [pureFuel] at run
  | succ fuel ih =>
    cases expression with
    | var v => simpa [pureFuel, pureExp] using (Option.some.inj run).symm
    | «let» xs body =>
      cases hb : pureFuel fuel n body with
      | none => simp [pureFuel, hb] at run
      | some value =>
        have bodyEq := ih body value hb
        cases value with
        | false =>
          simp [pureFuel, hb] at run
          subst result
          simp [pureExp, ← bodyEq]
        | true =>
          have listEq := foldPure_success_eq xs (pureFuel fuel n) (pureExp n) true result ih
            (by simpa [pureFuel, hb] using run)
          simpa [pureExp, ← pureExps_eq_all, ← bodyEq] using listEq
    | op op xs =>
      cases hp : pureOp op xs with
      | false =>
        simp [pureFuel, hp] at run
        subst result
        simp [pureExp, hp]
      | true =>
        have listEq := foldPure_success_eq xs (pureFuel fuel n) (pureExp n) true result ih
          (by simpa [pureFuel, hp] using run)
        simpa [pureExp, hp, ← pureExps_eq_all] using listEq
    | _ => simpa [pureFuel, pureExp] using (Option.some.inj run).symm

/-- The production retry computes the source purity result for every fuel. -/
theorem pureBounded_eq_pureExp (fuel n : Nat) (expression : Exp) :
    pureBounded fuel n expression = some (pureExp n expression) := by
  obtain ⟨result, run⟩ := pureBounded_succeeds fuel n expression
  cases first : pureFuel fuel n expression with
  | some value =>
    have equal := pureFuel_success_eq fuel n expression value first
    simp [pureBounded, first, equal]
  | none =>
    have retry : pureFuel (max fuel (expBudget expression + 1)) n expression = some result := by
      simpa [pureBounded, first] using run
    have equal := pureFuel_success_eq _ n expression result retry
    simpa [equal] using run

end Flapjack.Compiler.Backend.BviTmc
