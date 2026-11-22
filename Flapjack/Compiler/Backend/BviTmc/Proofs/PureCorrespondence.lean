module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.PureTotal

@[expose] public section

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

/-- HOL `pure_exps_sing`: the singleton list test is the single-expression
purity test. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "pure_exps_sing"]
theorem pureExps_sing (n : Nat) (h : Exp) : pureExps n [h] = pureExp n h := by
  simp [pureExps]

/-- HOL `pure_exps_cons`: a head and a tail are pure exactly when their
concatenation is. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "pure_exps_cons"]
theorem pureExps_cons (n : Nat) (h : Exp) (t : List Exp) :
    (pureExps n [h] && pureExps n t) = pureExps n (h :: t) := by
  simp [pureExps]

/-- HOL `pure_exps_eqns`: the source list test written without the auxiliary
single-expression test, one equation per constructor. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "pure_exps_eqns"]
theorem pureExps_eqns (n v : Nat) (e1 e2 e3 : Exp) (les : List Exp) (le : Exp)
    (re te : Exp) (ct : Nat) (cd : Option Nat) (cargs : List Exp) (ch : Option Exp)
    (fl fw la lb lc : Nat) (largs : List Exp) (lce : Exp) (res : List Exp)
    (oop : ClosLang.Op) (oargs : List Exp) (x1 x2 : Exp) (xs : List Exp) :
    pureExps n [] = true ∧
      pureExps n [.var v] = (v < n) ∧
      pureExps n [.ifThenElse e1 e2 e3] = false ∧
      pureExps n [.let les le] = (pureExps n [le] && pureExps n les) ∧
      pureExps n [.raise re] = false ∧
      pureExps n [.tick te] = false ∧
      pureExps n [.call ct cd cargs ch] = false ∧
      pureExps n [.force fl fw] = false ∧
      pureExps n [.letCall la lb lc largs lce] = false ∧
      pureExps n [.return res] = false ∧
      pureExps n [.op oop oargs] = (pureOp oop oargs && pureExps n oargs) ∧
      pureExps n (x1 :: x2 :: xs) = (pureExps n [x1] && pureExps n (x2 :: xs)) := by
  simp [pureExps, pureExp]

/-- HOL `pure_exp_eq`: the single-expression test is the singleton list test. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "pure_exp_eq"]
theorem pureExp_eq (n : Nat) (e : Exp) : pureExp n e = pureExps n [e] := by
  cases e
  all_goals simp [pureExps, pureExp]

/-- Concatenating pure lists is the conjunction of their purity tests. -/
private theorem pureExps_append_and (n : Nat) (xs ys : List Exp) :
    pureExps n (xs ++ ys) = (pureExps n xs && pureExps n ys) := by
  rw [pureExps_eq_all, List.all_append, ← pureExps_eq_all, ← pureExps_eq_all]

/-- HOL `pure_exps_append`: two pure lists concatenate to a pure list. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "pure_exps_append"]
theorem pureExps_append (n : Nat) (es1 es2 : List Exp)
    (h : (pureExps n es1 && pureExps n es2) = true) :
    pureExps n (es1 ++ es2) = true := by
  rw [pureExps_append_and]
  exact h

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
  cases first : pureFuel fuel n expression with
  | some value =>
    have equal := pureFuel_success_eq fuel n expression value first
    simp [pureBounded, first, equal]
  | none =>
    have enough : expBudget expression < max fuel (expBudget expression + 1) := by omega
    obtain ⟨result, retry⟩ := pureFuel_succeeds (max fuel (expBudget expression + 1)) n expression enough
    have equal := pureFuel_success_eq _ n expression result retry
    simp [pureBounded, first, retry, equal]

end Flapjack.Compiler.Backend.BviTmc
