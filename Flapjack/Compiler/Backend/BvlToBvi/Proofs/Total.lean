import Flapjack.Compiler.Backend.BvlToBvi.Compile
import Flapjack.Compiler.Backend.BviLet.Proofs.Total

/-! Structural sufficiency for the checked BVL-to-BVI traversal. These are
Flapjack infrastructure lemmas, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

private theorem destLet_budget (exp : Bvl.Exp) :
    listBudget (destLet exp).1 ≤ expBudget exp ∧ expBudget (destLet exp).2 ≤ expBudget exp := by
  cases exp <;> simp [destLet, expBudget, listBudget] <;> omega

private theorem compileAuxFuel_succeeds (fuel n args : Nat) (body : Bvi.Exp) :
    ∃ result, compileAuxFuel fuel n args body = some result := by
  obtain ⟨body', h⟩ := BviLet.compileBounded_succeeds fuel [] 0 body
  exact ⟨_, by simp [compileAuxFuel, h]; rfl⟩

mutual
/-- The BVL expression converter succeeds with a structural traversal bound,
independently of the budget supplied to the BVI let optimizer. -/
theorem compileFuel_succeeds (fuel optFuel n : Nat) (exp : Bvl.Exp)
    (bound : expBudget exp < fuel) : ∃ result, compileFuel fuel optFuel n exp = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases exp with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', a, n1⟩, hx⟩ := compileFuel_succeeds fuel optFuel n x bx
      obtain ⟨⟨y', b, n2⟩, hy⟩ := compileFuel_succeeds fuel optFuel n1 y by'
      obtain ⟨⟨z', c, n3⟩, hz⟩ := compileFuel_succeeds fuel optFuel n2 z bz
      exact ⟨_, by simp [compileFuel, hx, hy, hz]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', a, n1⟩, hx⟩ := compileFuel_succeeds fuel optFuel n x bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', a, n1⟩, hx⟩ := compileFuel_succeeds fuel optFuel n x bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨xs', a, n1⟩, hx⟩ := compileListFuel_succeeds fuel optFuel n xs bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨xs', a, n1⟩, hx⟩ := compileListFuel_succeeds fuel optFuel n xs bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | «let» xs body =>
      cases xs with
      | nil =>
        let args := (destLet body).1
        let inner := (destLet body).2
        have h : destLet body = (args, inner) := by simp [args, inner]
        have bd := destLet_budget body
        rw [h] at bd
        have ba : listBudget args < fuel := by simp_all [expBudget, listBudget] <;> omega
        have bi : expBudget inner < fuel := by simp_all [expBudget, listBudget] <;> omega
        obtain ⟨⟨args', a, n1⟩, ha⟩ := compileListFuel_succeeds fuel optFuel n args ba
        obtain ⟨⟨inner', b, n2⟩, hi⟩ := compileFuel_succeeds fuel optFuel n1 inner bi
        obtain ⟨extra, he⟩ := compileAuxFuel_succeeds optFuel n2 args'.length inner'
        exact ⟨_, by simp [compileFuel, h, ha, hi, he]; rfl⟩
      | cons x xs =>
        have ba : listBudget (x :: xs) < fuel := by simp_all [expBudget] <;> omega
        have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨args, a, n1⟩, ha⟩ := compileListFuel_succeeds fuel optFuel n (x :: xs) ba
        obtain ⟨⟨body', b, n2⟩, hb⟩ := compileFuel_succeeds fuel optFuel n1 body bb
        exact ⟨_, by simp [compileFuel, ha, hb]; rfl⟩
    | handle x y =>
      let args := (destLet x).1
      let inner := (destLet x).2
      have h : destLet x = (args, inner) := by simp [args, inner]
      have bd := destLet_budget x
      rw [h] at bd
      have ba : listBudget args < fuel := by simp_all [expBudget] <;> omega
      have bi : expBudget inner < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨args', a, n1⟩, ha⟩ := compileListFuel_succeeds fuel optFuel n args ba
      obtain ⟨⟨inner', b, n2⟩, hi⟩ := compileFuel_succeeds fuel optFuel n1 inner bi
      obtain ⟨⟨y', c, n3⟩, hy⟩ := compileFuel_succeeds fuel optFuel n2 y by'
      obtain ⟨extra, he⟩ := compileAuxFuel_succeeds optFuel n3 args'.length inner'
      exact ⟨_, by simp [compileFuel, h, ha, hi, hy, he]; rfl⟩
termination_by fuel

/-- The operand traversal also succeeds under its structural bound. -/
theorem compileListFuel_succeeds (fuel optFuel n : Nat) (xs : List Bvl.Exp)
    (bound : listBudget xs < fuel) : ∃ result, compileListFuel fuel optFuel n xs = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases xs with
    | nil => exact ⟨_, rfl⟩
    | cons x xs =>
      have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
      have bxs : listBudget xs < fuel := by simp_all [listBudget] <;> omega
      obtain ⟨⟨x', a, n1⟩, hx⟩ := compileFuel_succeeds fuel optFuel n x bx
      obtain ⟨⟨xs', b, n2⟩, hxs⟩ := compileListFuel_succeeds fuel optFuel n1 xs bxs
      exact ⟨_, by simp [compileListFuel, hx, hxs]; rfl⟩
termination_by fuel
end

/-- Retrying with the structural bound always produces a result. -/
theorem compileBounded_succeeds (fuel optFuel n : Nat) (exp : Bvl.Exp) :
    ∃ result, compileBounded fuel optFuel n exp = some result := by
  cases h : compileFuel fuel optFuel n exp with
  | some result => exact ⟨result, by simp [compileBounded, h]⟩
  | none =>
    have bound : expBudget exp < max fuel (expBudget exp + 1) := by omega
    obtain ⟨result, done⟩ := compileFuel_succeeds (max fuel (expBudget exp + 1)) optFuel n exp bound
    exact ⟨result, by simp [compileBounded, h, done]⟩

/-- The retry preserves the result of every successful original traversal. -/
theorem compileBounded_eq_of_success (fuel optFuel n : Nat) (exp : Bvl.Exp)
    (result : Bvi.Exp × List (Nat × Nat × Bvi.Exp) × Nat)
    (success : compileFuel fuel optFuel n exp = some result) :
    compileBounded fuel optFuel n exp = some result := by
  simp [compileBounded, success]

/-- Each labeled expression and its auxiliary code now lowers without a fuel
failure in either expression traversal or the BVI let optimizer. -/
theorem compileSingleFuel_succeeds (fuel optFuel n : Nat) (p : Nat × Nat × Bvl.Exp) :
    ∃ result, compileSingleFuel fuel optFuel n p = some result := by
  obtain ⟨name, args, exp⟩ := p
  obtain ⟨⟨exp', aux, n'⟩, h⟩ := compileBounded_succeeds fuel optFuel n exp
  obtain ⟨body, hb⟩ := BviLet.compileBounded_succeeds optFuel [] 0 exp'
  exact ⟨_, by simp [compileSingleFuel, h, hb]; rfl⟩

/-- Lowering a complete list of labeled expressions cannot exhaust either
traversal budget. -/
theorem compileProgramsFuel_succeeds (fuel optFuel n : Nat) (prog : List (Nat × Nat × Bvl.Exp)) :
    ∃ result, compileProgramsFuel fuel optFuel n prog = some result := by
  induction prog generalizing n with
  | nil => exact ⟨_, rfl⟩
  | cons p ps ih =>
    obtain ⟨⟨code, n'⟩, hc⟩ := compileSingleFuel_succeeds fuel optFuel n p
    obtain ⟨⟨rest, n''⟩, hr⟩ := ih n'
    exact ⟨_, by simp [compileProgramsFuel, hc, hr]; rfl⟩

/-- The executable whole-program BVL-to-BVI conversion cannot return `none`
because of traversal fuel. This is not the HOL pass correctness theorem. -/
theorem compileProgFuel_succeeds (fuel optFuel start n : Nat)
    (prog : List (Nat × Nat × Bvl.Exp)) :
    ∃ result, compileProgFuel fuel optFuel start n prog = some result := by
  obtain ⟨⟨code, n'⟩, h⟩ := compileProgramsFuel_succeeds fuel optFuel n prog
  exact ⟨_, by simp [compileProgFuel, h]; rfl⟩

end Flapjack.Compiler.Backend.BvlToBvi
