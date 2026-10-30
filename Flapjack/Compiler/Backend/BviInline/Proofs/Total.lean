import Flapjack.Compiler.Backend.BviInline

/-! Structural sufficiency for BVI inlining and tick removal. These lemmas
are Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BviInline
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

/-- Inlining succeeds under a structural bound, for arbitrary caches. -/
theorem inlineExpFuel_succeeds (fuel : Nat) (cache : Spt (Nat × Exp)) (exp : Exp)
    (bound : expBudget exp < fuel) : ∃ result, inlineExpFuel fuel cache exp = some result := by
  induction fuel generalizing exp with
  | zero => omega
  | succ fuel ih =>
    cases exp with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      obtain ⟨z', hz⟩ := ih z bz
      exact ⟨_, by simp [inlineExpFuel, hx, hy, hz]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [inlineExpFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [inlineExpFuel, hx]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (inlineExpFuel fuel cache) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      obtain ⟨body', hb⟩ := ih body bb
      exact ⟨_, by simp [inlineExpFuel, hy, hb]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (inlineExpFuel fuel cache) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      exact ⟨_, by simp [inlineExpFuel, hy]; rfl⟩
    | «return» xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (inlineExpFuel fuel cache) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      exact ⟨_, by simp [inlineExpFuel, hy]; rfl⟩
    | letCall rets ticks dest xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (inlineExpFuel fuel cache) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      obtain ⟨body', hb⟩ := ih body bb
      exact ⟨_, by simp [inlineExpFuel, hy, hb]; rfl⟩
    | call ticks target xs handler =>
      cases handler with
      | some h =>
        have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        have bh : expBudget h < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨ys, hy⟩ := mapM_succeeds xs (inlineExpFuel fuel cache) (by
          intro e he; apply ih; have := member_budget_lt xs e he; omega)
        obtain ⟨h', hh⟩ := ih h bh
        exact ⟨_, by simp [inlineExpFuel, hy, hh]; rfl⟩
      | none =>
        have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨ys, hy⟩ := mapM_succeeds xs (inlineExpFuel fuel cache) (by
          intro e he; apply ih; have := member_budget_lt xs e he; omega)
        cases target with
        | none => exact ⟨_, by simp [inlineExpFuel, hy]; rfl⟩
        | some name =>
          cases h : sptLookup name cache with
          | none => exact ⟨_, by simp [inlineExpFuel, hy, h]; rfl⟩
          | some entry =>
            obtain ⟨arity, body⟩ := entry
            by_cases eq : ys.length = arity
            · exact ⟨_, by simp [inlineExpFuel, hy, h, eq]; rfl⟩
            · exact ⟨_, by simp [inlineExpFuel, hy, h, eq]; rfl⟩

/-- Tick removal succeeds under a structural bound. -/
theorem removeTicksFuel_succeeds (fuel : Nat) (exp : Exp) (bound : expBudget exp < fuel) :
    ∃ result, removeTicksFuel fuel exp = some result := by
  induction fuel generalizing exp with
  | zero => omega
  | succ fuel ih =>
    cases exp with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      obtain ⟨z', hz⟩ := ih z bz
      exact ⟨_, by simp [removeTicksFuel, hx, hy, hz]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [removeTicksFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [removeTicksFuel, hx]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeTicksFuel fuel) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      obtain ⟨body', hb⟩ := ih body bb
      exact ⟨_, by simp [removeTicksFuel, hy, hb]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeTicksFuel fuel) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      exact ⟨_, by simp [removeTicksFuel, hy]; rfl⟩
    | «return» xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeTicksFuel fuel) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      exact ⟨_, by simp [removeTicksFuel, hy]; rfl⟩
    | letCall rets ticks dest xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeTicksFuel fuel) (by
        intro e he; apply ih; have := member_budget_lt xs e he; omega)
      obtain ⟨body', hb⟩ := ih body bb
      exact ⟨_, by simp [removeTicksFuel, hy, hb]; rfl⟩
    | call ticks target xs handler =>
      cases handler with
      | none =>
        have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeTicksFuel fuel) (by
          intro e he; apply ih; have := member_budget_lt xs e he; omega)
        exact ⟨_, by simp [removeTicksFuel, hy]; rfl⟩
      | some h =>
        have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        have bh : expBudget h < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeTicksFuel fuel) (by
          intro e he; apply ih; have := member_budget_lt xs e he; omega)
        obtain ⟨h', hh⟩ := ih h bh
        exact ⟨_, by simp [removeTicksFuel, hy, hh]; rfl⟩

/-- The production inliner cannot fail from traversal fuel. -/
theorem inlineExpBounded_succeeds (fuel : Nat) (cache : Spt (Nat × Exp)) (exp : Exp) :
    ∃ result, inlineExpBounded fuel cache exp = some result := by
  cases h : inlineExpFuel fuel cache exp with
  | some result => exact ⟨result, by simp [inlineExpBounded, h]⟩
  | none =>
    have bound : expBudget exp < max fuel (expBudget exp + 1) := by omega
    obtain ⟨result, done⟩ := inlineExpFuel_succeeds (max fuel (expBudget exp + 1)) cache exp bound
    exact ⟨result, by simp [inlineExpBounded, h, done]⟩

/-- The production tick remover cannot fail from traversal fuel. -/
theorem removeTicksBounded_succeeds (fuel : Nat) (exp : Exp) :
    ∃ result, removeTicksBounded fuel exp = some result := by
  cases h : removeTicksFuel fuel exp with
  | some result => exact ⟨result, by simp [removeTicksBounded, h]⟩
  | none =>
    have bound : expBudget exp < max fuel (expBudget exp + 1) := by omega
    obtain ⟨result, done⟩ := removeTicksFuel_succeeds (max fuel (expBudget exp + 1)) exp bound
    exact ⟨result, by simp [removeTicksBounded, h, done]⟩

/-- The retry preserves any successful original inlining result. -/
theorem inlineExpBounded_eq_of_success (fuel : Nat) (cache : Spt (Nat × Exp)) (exp result : Exp)
    (success : inlineExpFuel fuel cache exp = some result) :
    inlineExpBounded fuel cache exp = some result := by
  simp [inlineExpBounded, success]

/-- The retry preserves any successful original tick-removal result. -/
theorem removeTicksBounded_eq_of_success (fuel : Nat) (exp result : Exp)
    (success : removeTicksFuel fuel exp = some result) :
    removeTicksBounded fuel exp = some result := by
  simp [removeTicksBounded, success]

/-- The inliner succeeds over every program and initial cache. -/
theorem inlineAllFuel_succeeds (fuel : Nat) (cache : Spt (Nat × Exp))
    (prog : List (Nat × Nat × Exp)) : ∃ result, inlineAllFuel fuel cache prog = some result := by
  induction prog generalizing cache with
  | nil => exact ⟨_, rfl⟩
  | cons p ps ih =>
    obtain ⟨name, arity, body⟩ := p
    obtain ⟨body', hb⟩ := inlineExpBounded_succeeds fuel cache body
    obtain ⟨⟨next, rest⟩, hr⟩ := ih (if canonicalWrapper name arity body' then
      sptInsert name (arity, body') cache else cache)
    exact ⟨_, by simp [inlineAllFuel, hb, hr]; rfl⟩

/-- Whole-program inlining and tick removal cannot exhaust traversal fuel. -/
theorem compileProgFuel_succeeds (fuel : Nat) (prog : List (Nat × Nat × Exp)) :
    ∃ result, compileProgFuel fuel prog = some result := by
  obtain ⟨⟨cache, code⟩, h⟩ := inlineAllFuel_succeeds fuel .ln prog
  obtain ⟨code', hc⟩ := mapM_succeeds code (fun p => do
    pure (p.1, p.2.1, ← removeTicksBounded fuel p.2.2)) (by
      intro p _
      obtain ⟨name, arity, body⟩ := p
      obtain ⟨body', hb⟩ := removeTicksBounded_succeeds fuel body
      exact ⟨_, by simp [hb]; rfl⟩)
  refine ⟨(cache, code'), ?_⟩
  unfold compileProgFuel
  rw [h]
  change (code.mapM (fun (p : Nat × Nat × Exp) => do
    pure (p.1, p.2.1, ← removeTicksBounded fuel p.2.2))).bind
      (fun result => some (cache, result)) = some (cache, code')
  rw [hc]
  rfl

end Flapjack.Compiler.Backend.BviInline
