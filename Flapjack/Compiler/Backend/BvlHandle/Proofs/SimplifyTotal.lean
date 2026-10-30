import Flapjack.Compiler.Backend.BvlHandle.Proofs.HelpersTotal

/-! Structural sufficiency for handler simplification. These results are
Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BvlHandle
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

private theorem mapM_succeeds {α β : Type} (xs : List α) (f : α → Option β)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (by intro z hz; exact h z (by simp [hz]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

private theorem foldRaise_succeeds (xs : List Exp) (fuel : Nat) (init : Bool) :
    ∃ result, xs.foldlM (fun found e => if found then pure true else canRaiseBounded fuel e) init = some result := by
  induction xs generalizing init with
  | nil => exact ⟨init, rfl⟩
  | cons x xs ih =>
    cases init with
    | true =>
      obtain ⟨result, hr⟩ := ih true
      exact ⟨result, by simpa using hr⟩
    | false =>
      obtain ⟨value, hv⟩ := canRaiseBounded_succeeds fuel x
      obtain ⟨result, hr⟩ := ih value
      exact ⟨result, by simpa [hv] using hr⟩

mutual
/-- Handler simplification succeeds under a structural fuel bound. -/
theorem simplifyFuel_succeeds (fuel : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, simplifyFuel fuel e = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases e with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := simplifyFuel_succeeds fuel x bx
      obtain ⟨y', hy⟩ := simplifyFuel_succeeds fuel y by'
      obtain ⟨z', hz⟩ := simplifyFuel_succeeds fuel z bz
      exact ⟨_, by simp [simplifyFuel, hx, hy, hz]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (simplifyFuel fuel) (by
        intro x hx; apply simplifyFuel_succeeds; have := member_budget_lt xs x hx; omega)
      obtain ⟨body', hb⟩ := simplifyFuel_succeeds fuel body bb
      exact ⟨_, by simp [simplifyFuel, hy, hb]; rfl⟩
    | handle x handler =>
      have bh : expBudget x + expBudget handler + 1 < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := makeHandleFuel_succeeds fuel x handler 0 bh
      exact ⟨_, by simpa [simplifyFuel] using h⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := simplifyFuel_succeeds fuel x bx
      exact ⟨_, by simp [simplifyFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := simplifyFuel_succeeds fuel x bx
      exact ⟨_, by simp [simplifyFuel, hx]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (simplifyFuel fuel) (by
        intro x hx; apply simplifyFuel_succeeds; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [simplifyFuel, hy]; rfl⟩
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (simplifyFuel fuel) (by
        intro x hx; apply simplifyFuel_succeeds; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [simplifyFuel, hy]; rfl⟩
termination_by fuel

/-- Moving a handler succeeds when fuel covers both input expressions. -/
theorem makeHandleFuel_succeeds (fuel : Nat) (x handler : Exp) (depth : Nat)
    (bound : expBudget x + expBudget handler + 1 < fuel) :
    ∃ result, makeHandleFuel fuel x handler depth = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    have bx : expBudget x < fuel := by omega
    have bh : expBudget handler < fuel := by omega
    obtain ⟨x', hx⟩ := simplifyFuel_succeeds fuel x bx
    obtain ⟨handler', hh⟩ := simplifyFuel_succeeds fuel handler bh
    obtain ⟨adjusted, ha⟩ := adjustVarsBounded_succeeds fuel 1 depth handler'
    cases x with
    | raise r =>
      obtain ⟨raises, hr⟩ := canRaiseBounded_succeeds fuel r
      cases raises <;> exact ⟨_, by simp [makeHandleFuel, hx, hh, ha, hr]; rfl⟩
    | «let» xs body =>
      have bb : expBudget body + expBudget handler + 1 < fuel := by simp_all [expBudget] <;> omega
      have bl : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨raises, hr⟩ := foldRaise_succeeds xs fuel false
      simp only [Option.pure_def] at hr
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (simplifyFuel fuel) (by
        intro e he; apply simplifyFuel_succeeds; have := member_budget_lt xs e he; omega)
      obtain ⟨body', hbody⟩ := makeHandleFuel_succeeds fuel body handler (depth + xs.length) bb
      cases raises <;> exact ⟨_, by simp [makeHandleFuel, hx, hh, ha, hr, hy, hbody]; rfl⟩
    | ifThenElse cond yes no =>
      have bc : expBudget cond < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget yes < fuel := by simp_all [expBudget] <;> omega
      have bn : expBudget no < fuel := by simp_all [expBudget] <;> omega
      have byh : expBudget yes + expBudget handler + 1 < fuel := by simp_all [expBudget] <;> omega
      have bnh : expBudget no + expBudget handler + 1 < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨cr, hc⟩ := canRaiseBounded_succeeds fuel cond
      obtain ⟨yr, hy⟩ := canRaiseBounded_succeeds fuel yes
      obtain ⟨nr, hn⟩ := canRaiseBounded_succeeds fuel no
      obtain ⟨cond', hc'⟩ := simplifyFuel_succeeds fuel cond bc
      obtain ⟨yes', hy'⟩ := simplifyFuel_succeeds fuel yes by'
      obtain ⟨no', hn'⟩ := simplifyFuel_succeeds fuel no bn
      obtain ⟨yes'', hy''⟩ := makeHandleFuel_succeeds fuel yes handler depth byh
      obtain ⟨no'', hn''⟩ := makeHandleFuel_succeeds fuel no handler depth bnh
      cases cr <;> cases yr <;> cases nr <;>
        exact ⟨_, by simp [makeHandleFuel, hx, hh, ha, hc, hy, hn, hc', hy', hn', hy'', hn'']; rfl⟩
    | _ => exact ⟨_, by simp [makeHandleFuel, hx, hh, ha]; rfl⟩
termination_by fuel
end

/-- The executable simplifier cannot exhaust traversal fuel. -/
theorem simplifyBounded_succeeds (fuel : Nat) (e : Exp) :
    ∃ result, simplifyBounded fuel e = some result := by
  cases h : simplifyFuel fuel e with
  | some result => exact ⟨result, by simp [simplifyBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := simplifyFuel_succeeds (max fuel (expBudget e + 1)) e bound
    exact ⟨result, by simp [simplifyBounded, h, done]⟩

/-- Previously successful simplifications are preserved by the retry. -/
theorem simplifyBounded_eq_of_success (fuel : Nat) (e result : Exp)
    (success : simplifyFuel fuel e = some result) : simplifyBounded fuel e = some result := by
  simp [simplifyBounded, success]

end Flapjack.Compiler.Backend.BvlHandle
