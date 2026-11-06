import Flapjack.Compiler.Backend.ClosFvs
import Flapjack.Compiler.Backend.ClosLang.Proofs.Budget

/-! Structural sufficiency for closure free-variable cleanup. These results are
Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open ClosLang

/-- Free-variable cleanup succeeds under a structural fuel bound. -/
theorem removeFuel_succeeds (fuel depth : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, removeFuel fuel depth e = some result := by
  induction fuel generalizing depth e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var t v => exact ⟨_, rfl⟩
    | ifThenElse t x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih depth x bx
      obtain ⟨y', hy⟩ := ih depth y by'
      obtain ⟨z', hz⟩ := ih depth z bz
      exact ⟨_, by simp [removeFuel, hx, hy, hz]; rfl⟩
    | «let» t xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeFuel fuel depth) (by
        intro x hx; apply ih depth; have := member_budget_lt xs x hx; omega)
      have length := mapM_length xs (removeFuel fuel depth) ys hy
      obtain ⟨body', hb⟩ := ih (depth + xs.length) body bb
      exact ⟨_, by simp [removeFuel, hy, length, hb]; rfl⟩
    | raise t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih depth x bx
      exact ⟨_, by simp [removeFuel, hx]; rfl⟩
    | tick t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih depth x bx
      exact ⟨_, by simp [removeFuel, hx]; rfl⟩
    | handle t x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih depth x bx
      obtain ⟨y', hy⟩ := ih (depth + 1) y by'
      exact ⟨_, by simp [removeFuel, hx, hy]; rfl⟩
    | op t op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeFuel fuel depth) (by
        intro x hx; apply ih depth; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [removeFuel, hy]; rfl⟩
    | call t ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeFuel fuel depth) (by
        intro x hx; apply ih depth; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [removeFuel, hy]; rfl⟩
    | app t loc x xs =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih depth x bx
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeFuel fuel depth) (by
        intro y hy; apply ih depth; have := member_budget_lt xs y hy; omega)
      exact ⟨_, by simp [removeFuel, hx, hy]; rfl⟩
    | fn name loc vs arity body =>
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨body', hb⟩ := ih (arity + (vs.map List.length).getD depth) body bb
      exact ⟨_, by simp [removeFuel, hb]; rfl⟩
    | letrec names loc vs fns body =>
      have bf : funsBudget fns < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨fs, hf⟩ := mapM_succeeds fns (fun p => do pure (p.1, ← removeFuel fuel (p.1 + fns.length + (vs.map List.length).getD depth) p.2)) (by
        intro p hp; obtain ⟨arity, e⟩ := p
        obtain ⟨e', he⟩ := ih (arity + fns.length + (vs.map List.length).getD depth) e (by have := fun_member_budget_lt fns arity e hp; omega)
        exact ⟨_, by simp [he]; rfl⟩)
      obtain ⟨body', hb⟩ := ih (fns.length + depth) body bb
      refine ⟨.letrec names loc vs fs body', ?_⟩
      simp only [removeFuel]
      change (fns.mapM (fun (p : Nat × Exp) => do pure (p.1, ← removeFuel fuel (p.1 + fns.length + (vs.map List.length).getD depth) p.2))).bind
        (fun fs => (removeFuel fuel (fns.length + depth) body).bind (fun body => some (Exp.letrec names loc vs fs body))) = _
      rw [hf, hb]
      rfl

/-- The executable retry cannot exhaust free-variable cleanup fuel. -/
theorem removeBounded_succeeds (fuel depth : Nat) (e : Exp) :
    ∃ result, removeBounded fuel depth e = some result := by
  cases h : removeFuel fuel depth e with
  | some result => exact ⟨result, by simp [removeBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := removeFuel_succeeds (max fuel (expBudget e + 1)) depth e bound
    exact ⟨result, by simp [removeBounded, h, done]⟩

/-- Retrying preserves every previously successful free-variable cleanup result. -/
theorem removeBounded_eq_of_success (fuel depth : Nat) (e result : Exp)
    (success : removeFuel fuel depth e = some result) : removeBounded fuel depth e = some result := by
  simp [removeBounded, success]

end Flapjack.Compiler.Backend.ClosFvs
