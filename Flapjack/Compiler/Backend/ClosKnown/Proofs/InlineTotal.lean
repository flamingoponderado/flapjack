import Flapjack.Compiler.Backend.ClosKnown.Inline
import Flapjack.Compiler.Backend.ClosLang.Proofs.Budget
import Flapjack.Compiler.Backend.ClosCall.Proofs.FreeTotal

/-! Structural sufficiency of known-closure inlining analyses. These are
Flapjack infrastructure lemmas, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

private theorem bodies_budget (fns : List (Nat × Exp)) :
    listBudget (fns.map Prod.snd) = funsBudget fns := by
  induction fns with
  | nil => simp [listBudget, funsBudget]
  | cons p ps ih =>
    obtain ⟨arity, body⟩ := p
    simp [listBudget, funsBudget, ih]

private theorem foldSum_succeeds (xs : List Exp) (f : Exp → Option Nat) (initial : Nat)
    (h : ∀ x ∈ xs, ∃ result, f x = some result) :
    ∃ result, xs.foldlM (fun n x => do pure (n + (← f x))) initial = some result := by
  induction xs generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons x xs ih =>
    obtain ⟨value, hv⟩ := h x (by simp)
    obtain ⟨result, hr⟩ := ih (initial + value) (by intro y hy; exact h y (by simp [hy]))
    exact ⟨result, by simpa [hv] using hr⟩

private theorem foldAny_succeeds (xs : List Exp) (f : Exp → Option Bool) (initial : Bool)
    (h : ∀ x ∈ xs, ∃ result, f x = some result) :
    ∃ result, xs.foldlM (fun found x => if found then pure true else f x) initial = some result := by
  induction xs generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons x xs ih =>
    cases initial with
    | true =>
      obtain ⟨result, hr⟩ := ih true (by intro y hy; exact h y (by simp [hy]))
      exact ⟨result, by simpa using hr⟩
    | false =>
      obtain ⟨value, hv⟩ := h x (by simp)
      obtain ⟨result, hr⟩ := ih value (by intro y hy; exact h y (by simp [hy]))
      exact ⟨result, by simpa [hv] using hr⟩

/-- The closure size metric succeeds under a structural fuel bound. -/
theorem sizeFuel_succeeds (fuel : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, sizeFuel fuel e = some result := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var t v => exact ⟨_, rfl⟩
    | tick t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih x bx
      exact ⟨_, by simp [sizeFuel, h]; rfl⟩
    | raise t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih x bx
      exact ⟨_, by simp [sizeFuel, h]; rfl⟩
    | fn name loc vs arity body =>
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih body bb
      exact ⟨_, by simp [sizeFuel, h]; rfl⟩
    | ifThenElse t x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      obtain ⟨z', hz⟩ := ih z bz
      exact ⟨_, by simp [sizeFuel, hx, hy, hz]; rfl⟩
    | «let» t xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨sum, hs⟩ := foldSum_succeeds xs (sizeFuel fuel) 0 (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      simp at hs
      obtain ⟨body', hb⟩ := ih body bb
      exact ⟨_, by simp [sizeFuel, hs, hb]; rfl⟩
    | handle t x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      exact ⟨_, by simp [sizeFuel, hx, hy]; rfl⟩
    | op t op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨sum, hs⟩ := foldSum_succeeds xs (sizeFuel fuel) 0 (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      simp at hs
      exact ⟨_, by simp [sizeFuel, hs]; rfl⟩
    | call t ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨sum, hs⟩ := foldSum_succeeds xs (sizeFuel fuel) 0 (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      simp at hs
      exact ⟨_, by simp [sizeFuel, hs]; rfl⟩
    | app t loc x xs =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨sum, hs⟩ := foldSum_succeeds xs (sizeFuel fuel) 0 (by
        intro y hy; apply ih; have := member_budget_lt xs y hy; omega)
      simp at hs
      exact ⟨_, by simp [sizeFuel, hx, hs]; rfl⟩
    | letrec names loc vs fns body =>
      have bf : funsBudget fns < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      have bs : listBudget (fns.map Prod.snd) < fuel := by rw [bodies_budget]; exact bf
      obtain ⟨sum, hs⟩ := foldSum_succeeds (fns.map Prod.snd) (sizeFuel fuel) 0 (by
        intro x hx; apply ih; have := member_budget_lt (fns.map Prod.snd) x hx; omega)
      simp at hs
      obtain ⟨body', hb⟩ := ih body bb
      exact ⟨_, by simp [sizeFuel, hs, hb]; rfl⟩

/-- Closure-presence detection succeeds under a structural fuel bound. -/
theorem containsClosuresFuel_succeeds (fuel : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, containsClosuresFuel fuel e = some result := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var t v => exact ⟨_, rfl⟩
    | fn name loc vs arity body => exact ⟨_, rfl⟩
    | letrec names loc vs fns body => exact ⟨_, rfl⟩
    | raise t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih x bx
      exact ⟨_, by simp [containsClosuresFuel, h]; rfl⟩
    | tick t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih x bx
      exact ⟨_, by simp [containsClosuresFuel, h]; rfl⟩
    | ifThenElse t x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldAny_succeeds [x, y, z] (containsClosuresFuel fuel) false (by
        intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> first | exact ih _ bx | exact ih _ by' | exact ih _ bz)
      exact ⟨result, by simpa [containsClosuresFuel] using h⟩
    | «let» t xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldAny_succeeds (xs ++ [body]) (containsClosuresFuel fuel) false (by
        intro e he; simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · apply ih; have := member_budget_lt xs e he; omega
        · exact ih _ bb)
      exact ⟨result, by simpa [containsClosuresFuel] using h⟩
    | handle t x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldAny_succeeds [x, y] (containsClosuresFuel fuel) false (by
        intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> first | exact ih _ bx | exact ih _ by')
      exact ⟨result, by simpa [containsClosuresFuel] using h⟩
    | op t op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldAny_succeeds xs (containsClosuresFuel fuel) false (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨result, by simpa [containsClosuresFuel] using h⟩
    | call t ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldAny_succeeds xs (containsClosuresFuel fuel) false (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨result, by simpa [containsClosuresFuel] using h⟩
    | app t loc x xs =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldAny_succeeds (x :: xs) (containsClosuresFuel fuel) false (by
        intro e he; simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact ih _ bx
        · apply ih; have := member_budget_lt xs e he; omega)
      exact ⟨result, by simpa [containsClosuresFuel] using h⟩

/-- Retried size analysis cannot exhaust traversal fuel. -/
theorem sizeBounded_succeeds (fuel : Nat) (e : Exp) : ∃ result, sizeBounded fuel e = some result := by
  cases h : sizeFuel fuel e with
  | some result => exact ⟨result, by simp [sizeBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := sizeFuel_succeeds (max fuel (expBudget e + 1)) e bound
    exact ⟨result, by simp [sizeBounded, h, done]⟩

/-- Retried closure detection cannot exhaust traversal fuel. -/
theorem containsClosuresBounded_succeeds (fuel : Nat) (e : Exp) :
    ∃ result, containsClosuresBounded fuel e = some result := by
  cases h : containsClosuresFuel fuel e with
  | some result => exact ⟨result, by simp [containsClosuresBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := containsClosuresFuel_succeeds (max fuel (expBudget e + 1)) e bound
    exact ⟨result, by simp [containsClosuresBounded, h, done]⟩

/-- Retrying preserves previously successful size results. -/
theorem sizeBounded_eq_of_success (fuel : Nat) (e : Exp) (result : Nat)
    (success : sizeFuel fuel e = some result) : sizeBounded fuel e = some result := by
  simp [sizeBounded, success]

/-- Retrying preserves previously successful closure-presence results. -/
theorem containsClosuresBounded_eq_of_success (fuel : Nat) (e : Exp) (result : Bool)
    (success : containsClosuresFuel fuel e = some result) : containsClosuresBounded fuel e = some result := by
  simp [containsClosuresBounded, success]

/-- Constructing an approximation cannot fail from size-analysis fuel. -/
theorem closApproxFuel_succeeds (fuel maxSize loc arity : Nat) (body : Exp) :
    ∃ result, closApproxFuel fuel maxSize loc arity body = some result := by
  obtain ⟨size, h⟩ := sizeBounded_succeeds fuel body
  exact ⟨_, by simp [closApproxFuel, h]; rfl⟩

/-- An inlining decision cannot fail from closure or free-variable traversal fuel. -/
theorem decideInlineFuel_succeeds (fuel : Nat) (c : Config) (approx : ValApprox)
    (loc : Option Nat) (arity : Nat) : ∃ result, decideInlineFuel fuel c approx loc arity = some result := by
  cases loc with
  | some loc => exact ⟨_, by simp [decideInlineFuel]; rfl⟩
  | none =>
    cases approx with
    | clos target n body size =>
      obtain ⟨contains, hc⟩ := containsClosuresBounded_succeeds fuel body
      obtain ⟨closed, hf⟩ := ClosCall.closedFuel_succeeds fuel
        (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity body)
      cases contains <;> cases closed <;> simp [decideInlineFuel, hc, hf] <;>
        repeat' (first | split | exact ⟨_, rfl⟩)
    | _ => simp [decideInlineFuel] <;> repeat' (first | split | exact ⟨_, rfl⟩)

end Flapjack.Compiler.Backend.ClosKnown
