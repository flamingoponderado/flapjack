import Flapjack.Compiler.Backend.BvlInline
import Flapjack.Compiler.Backend.ListFoldTotal

/-! Structural sufficiency for the BVL inliner's recursion test. These are
Flapjack infrastructure lemmas, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl BvlToBvi

private theorem member_budget_lt (xs : List Exp) (e : Exp) (h : e ∈ xs) :
    expBudget e < listBudget xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [listBudget]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

/-- Recursion detection succeeds under a structural traversal bound. -/
theorem recursiveFuel_succeeds (fuel name : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, recursiveFuel fuel name e = some result := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih x bx
      exact ⟨_, by simp [recursiveFuel, h]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih x bx
      exact ⟨_, by simp [recursiveFuel, h]; rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldRec_succeeds [x, y, z] (recursiveFuel fuel name) false (by
        intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> first | exact ih _ bx | exact ih _ by' | exact ih _ bz)
      exact ⟨result, by simpa [recursiveFuel] using h⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldRec_succeeds (xs ++ [body]) (recursiveFuel fuel name) false (by
        intro e he; simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · apply ih; have := member_budget_lt xs e he; omega
        · exact ih _ bb)
      exact ⟨result, by simpa [recursiveFuel] using h⟩
    | handle x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldRec_succeeds [x, y] (recursiveFuel fuel name) false (by
        intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> first | exact ih _ bx | exact ih _ by')
      exact ⟨result, by simpa [recursiveFuel] using h⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldRec_succeeds xs (recursiveFuel fuel name) false (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨result, by simpa [recursiveFuel] using h⟩
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldRec_succeeds xs (recursiveFuel fuel name) false (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      cases equal : (dest == some name) with
      | false => exact ⟨result, by simpa [recursiveFuel, equal] using h⟩
      | true => exact ⟨true, by simp [recursiveFuel, equal]⟩

end Flapjack.Compiler.Backend.BvlInline
