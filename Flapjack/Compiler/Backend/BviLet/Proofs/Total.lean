import Flapjack.Compiler.Backend.BviLet.Compile
import Flapjack.Compiler.Backend.Bvi.Budget

/-! Structural sufficiency for the BVI let optimizer. This is Flapjack
infrastructure and does not assert HOL correspondence. -/
namespace Flapjack.Compiler.Backend.BviLet
open Bvi

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

private theorem mapM_succeeds {α β : Type} (xs : List α) (f : α → Option β)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (by intro z hz; exact h z (by simp [hz]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- The optimizer succeeds whenever its fuel exceeds the BVI structural
budget, for every environment and offset. -/
theorem compileFuel_succeeds (fuel : Nat) (env : List Nat) (d : Nat) (exp : Exp)
    (bound : expBudget exp < fuel) : ∃ result, compileFuel fuel env d exp = some result := by
  induction fuel generalizing env d exp with
  | zero => omega
  | succ fuel ih =>
    cases exp with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih env d x bx
      obtain ⟨y', hy⟩ := ih env d y by'
      obtain ⟨z', hz⟩ := ih env d z bz
      exact ⟨_, by simp [compileFuel, hx, hy, hz]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih env d x bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih env d x bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel env d) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      exact ⟨_, by simp [compileFuel, hy]; rfl⟩
    | «return» xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel env d) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      exact ⟨_, by simp [compileFuel, hy]; rfl⟩
    | call ticks dest xs handler =>
      cases handler with
      | none =>
        have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel env d) (by
          intro e he; apply ih; have := member_budget_lt xs e he; omega)
        exact ⟨_, by simp [compileFuel, hy]; rfl⟩
      | some h =>
        have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        have bh : expBudget h < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel env d) (by
          intro e he; apply ih; have := member_budget_lt xs e he; omega)
        obtain ⟨h', hh⟩ := ih (0 :: env) d h bh
        exact ⟨_, by simp [compileFuel, hy, hh]; rfl⟩
    | letCall rets ticks dest xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel env d) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      obtain ⟨body', hb⟩ := ih (List.replicate rets 0 ++ env) d body bb
      exact ⟨_, by simp [compileFuel, hy, hb]; rfl⟩
    | «let» xs body =>
      cases xs with
      | nil =>
        have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨body', hb⟩ := ih env d body bb
        exact ⟨_, by simp [compileFuel, hb]; rfl⟩
      | cons x xs =>
        have bx : listBudget (x :: xs) < fuel := by simp_all [expBudget] <;> omega
        have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
        have each : ∀ e ∈ x :: xs, expBudget e < fuel := by
          intro e he; have := member_budget_lt (x :: xs) e he; omega
        cases body with
        | var v =>
          by_cases eq : v = xs.length
          · cases hlast : (x :: xs).getLast? with
            | none =>
              have := List.getLast?_eq_none_iff.mp hlast
              simp at this
            | some last =>
              have lastmem : last ∈ x :: xs := by
                obtain ⟨ys, h⟩ := List.getLast?_eq_some_iff.mp hlast
                rw [h]; simp
              obtain ⟨earlier, hearlier⟩ := mapM_succeeds (x :: xs).dropLast (compileFuel fuel env d) (by
                intro e he; apply ih; exact each e (List.dropLast_subset _ he))
              obtain ⟨last', hlast'⟩ := ih (env.map ((x :: xs).length - 1 + ·))
                (d + ((x :: xs).length - 1)) last (each last lastmem)
              simp only [List.length_cons, Nat.add_sub_cancel] at hlast'
              exact ⟨_, by simp [compileFuel, eq, hlast, hearlier, hlast']; rfl⟩
          · obtain ⟨ys, hy⟩ := mapM_succeeds (x :: xs) (compileFuel fuel env d) (by
              intro e he; exact ih env d e (each e he))
            obtain ⟨body', hb⟩ := ih (extractList ys ++ env) d (.var v) bb
            exact ⟨_, by simp [compileFuel, eq, hy, hb]; rfl⟩
        | _ =>
          obtain ⟨ys, hy⟩ := mapM_succeeds (x :: xs) (compileFuel fuel env d) (by
            intro e he; exact ih env d e (each e he))
          obtain ⟨body', hb⟩ := ih (extractList ys ++ env) d _ bb
          exact ⟨_, by simp [compileFuel, hy, hb]; rfl⟩

/-- The production retry cannot fail due to an insufficient traversal bound. -/
theorem compileBounded_succeeds (fuel : Nat) (env : List Nat) (d : Nat) (exp : Exp) :
    ∃ result, compileBounded fuel env d exp = some result := by
  cases h : compileFuel fuel env d exp with
  | some result => exact ⟨result, by simp [compileBounded, h]⟩
  | none =>
    have bound : expBudget exp < max fuel (expBudget exp + 1) := by omega
    obtain ⟨result, done⟩ := compileFuel_succeeds (max fuel (expBudget exp + 1)) env d exp bound
    exact ⟨result, by simp [compileBounded, h, done]⟩

/-- The retry preserves all results obtained with the original fuel. -/
theorem compileBounded_eq_of_success (fuel : Nat) (env : List Nat) (d : Nat)
    (exp result : Exp) (success : compileFuel fuel env d exp = some result) :
    compileBounded fuel env d exp = some result := by
  simp [compileBounded, success]

end Flapjack.Compiler.Backend.BviLet
