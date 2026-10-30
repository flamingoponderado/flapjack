import Flapjack.Compiler.Backend.ClosLetop
import Flapjack.Compiler.Backend.ClosLang.Proofs.Budget

/-! Structural sufficiency for closure let-operation cleanup. These results are
Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang

/-- Let-operation cleanup succeeds under a structural fuel bound. -/
theorem compileFuel_succeeds (fuel : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, compileFuel fuel e = some result := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var t v => exact ⟨_, rfl⟩
    | ifThenElse t x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      obtain ⟨z', hz⟩ := ih z bz
      exact ⟨_, by simp [compileFuel, hx, hy, hz]; rfl⟩
    | «let» t xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      obtain ⟨body', hb⟩ := ih body bb
      cases body' <;> simp [compileFuel, hy, hb] <;> repeat' (first | split | exact ⟨_, rfl⟩)
    | raise t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | tick t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | handle t x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      exact ⟨_, by simp [compileFuel, hx, hy]; rfl⟩
    | op t op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [compileFuel, hy]; rfl⟩
    | call t ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [compileFuel, hy]; rfl⟩
    | app t loc x xs =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel) (by
        intro y hy; apply ih; have := member_budget_lt xs y hy; omega)
      exact ⟨_, by simp [compileFuel, hx, hy]; rfl⟩
    | fn name loc vs arity body =>
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨body', hb⟩ := ih body bb
      exact ⟨_, by simp [compileFuel, hb]; rfl⟩
    | letrec names loc vs fns body =>
      have bf : funsBudget fns < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨fs, hf⟩ := mapM_succeeds fns (fun p => do pure (p.1, ← compileFuel fuel p.2)) (by
        intro p hp; obtain ⟨arity, e⟩ := p
        obtain ⟨e', he⟩ := ih e (by have := fun_member_budget_lt fns arity e hp; omega)
        exact ⟨_, by simp [he]; rfl⟩)
      obtain ⟨body', hb⟩ := ih body bb
      refine ⟨.letrec names loc vs fs body', ?_⟩
      simp only [compileFuel]
      change (fns.mapM (fun (p : Nat × Exp) => do pure (p.1, ← compileFuel fuel p.2))).bind
        (fun fs => (compileFuel fuel body).bind (fun body => some (Exp.letrec names loc vs fs body))) = _
      rw [hf, hb]
      rfl

/-- The executable retry cannot exhaust let-operation fuel. -/
theorem compileBounded_succeeds (fuel : Nat) (e : Exp) :
    ∃ result, compileBounded fuel e = some result := by
  cases h : compileFuel fuel e with
  | some result => exact ⟨result, by simp [compileBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := compileFuel_succeeds (max fuel (expBudget e + 1)) e bound
    exact ⟨result, by simp [compileBounded, h, done]⟩

/-- Retrying preserves every previously successful let-operation result. -/
theorem compileBounded_eq_of_success (fuel : Nat) (e result : Exp)
    (success : compileFuel fuel e = some result) : compileBounded fuel e = some result := by
  simp [compileBounded, success]

end Flapjack.Compiler.Backend.ClosLetop
