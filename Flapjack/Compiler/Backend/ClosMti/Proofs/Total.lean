import Flapjack.Compiler.Backend.ClosMti.Proofs.Budget

/-! Structural sufficiency for multi-argument closure introduction. These
are Flapjack infrastructure lemmas, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang

/-- Multi-argument introduction succeeds under a structural traversal bound. -/
theorem introMultiFuel_succeeds (fuel maxApp : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, introMultiFuel fuel maxApp e = some result := by
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
      exact ⟨_, by simp [introMultiFuel, hx, hy, hz]; rfl⟩
    | «let» t xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (introMultiFuel fuel maxApp) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      obtain ⟨body', hb⟩ := ih body bb
      exact ⟨_, by simp [introMultiFuel, hy, hb]; rfl⟩
    | raise t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [introMultiFuel, hx]; rfl⟩
    | tick t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [introMultiFuel, hx]; rfl⟩
    | handle t x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      exact ⟨_, by simp [introMultiFuel, hx, hy]; rfl⟩
    | op t op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (introMultiFuel fuel maxApp) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [introMultiFuel, hy]; rfl⟩
    | call t ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (introMultiFuel fuel maxApp) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [introMultiFuel, hy]; rfl⟩
    | app t loc x xs =>
      cases loc with
      | some loc =>
        have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
        have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨x', hx⟩ := ih x bx
        obtain ⟨ys, hy⟩ := mapM_succeeds xs (introMultiFuel fuel maxApp) (by
          intro y hy; apply ih; have := member_budget_lt xs y hy; omega)
        exact ⟨_, by simp [introMultiFuel, hx, hy]; rfl⟩
      | none =>
        let args := (collectApps maxApp xs x).1
        let head := (collectApps maxApp xs x).2
        have collected : collectApps maxApp xs x = (args, head) := by simp [args, head]
        have b := collectApps_budget maxApp xs x
        rw [collected] at b
        have bh : expBudget head < fuel := by simp_all [expBudget] <;> omega
        have ba : listBudget args < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨head', hh⟩ := ih head bh
        obtain ⟨args', ha⟩ := mapM_succeeds args (introMultiFuel fuel maxApp) (by
          intro y hy; apply ih; have := member_budget_lt args y hy; omega)
        exact ⟨_, by simp [introMultiFuel, collected, hh, ha]; rfl⟩
    | fn name loc vs arity body =>
      cases loc with
      | some loc =>
        have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨body', hb⟩ := ih body bb
        exact ⟨_, by simp [introMultiFuel, hb]; rfl⟩
      | none =>
        cases vs with
        | some vs =>
          have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
          obtain ⟨body', hb⟩ := ih body bb
          exact ⟨_, by simp [introMultiFuel, hb]; rfl⟩
        | none =>
          let arity' := (collectArgs maxApp arity body).1
          let inner := (collectArgs maxApp arity body).2
          have collected : collectArgs maxApp arity body = (arity', inner) := by simp [arity', inner]
          have b := collectArgs_budget maxApp arity body
          rw [collected] at b
          have bi : expBudget inner < fuel := by simp_all [expBudget] <;> omega
          obtain ⟨inner', hi⟩ := ih inner bi
          exact ⟨_, by simp [introMultiFuel, collected, hi]; rfl⟩
    | letrec names loc vs fns body =>
      have bf : funsBudget fns < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨body', hb⟩ := ih body bb
      cases loc with
      | some loc => exact ⟨_, by simp [introMultiFuel, hb]; rfl⟩
      | none =>
        cases vs with
        | some vs => exact ⟨_, by simp [introMultiFuel, hb]; rfl⟩
        | none =>
          obtain ⟨fs, hf⟩ := mapM_succeeds fns (fun p => do
            let (arity, inner) := collectArgs maxApp p.1 p.2
            pure (arity, ← introMultiFuel fuel maxApp inner)) (by
              intro p hp; obtain ⟨arity, e⟩ := p
              let arity' := (collectArgs maxApp arity e).1
              let inner := (collectArgs maxApp arity e).2
              have collected : collectArgs maxApp arity e = (arity', inner) := by simp [arity', inner]
              have b := collectArgs_budget maxApp arity e
              rw [collected] at b
              simp only at b
              have member := fun_member_budget_lt fns arity e hp
              obtain ⟨inner', hi⟩ := ih inner (by omega)
              exact ⟨_, by simp [collected, hi]; rfl⟩)
          refine ⟨.letrec names none none fs body', ?_⟩
          simp only [introMultiFuel]
          change (fns.mapM (fun (p : Nat × Exp) => do
            let (arity, inner) := collectArgs maxApp p.1 p.2
            pure (arity, ← introMultiFuel fuel maxApp inner))).bind
              (fun fs => (introMultiFuel fuel maxApp body).bind
                (fun body => some (Exp.letrec names none none fs body))) = _
          rw [hf, hb]
          rfl

/-- The production retry cannot exhaust multi-argument traversal fuel. -/
theorem introMultiBounded_succeeds (fuel maxApp : Nat) (e : Exp) :
    ∃ result, introMultiBounded fuel maxApp e = some result := by
  cases h : introMultiFuel fuel maxApp e with
  | some result => exact ⟨result, by simp [introMultiBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := introMultiFuel_succeeds (max fuel (expBudget e + 1)) maxApp e bound
    exact ⟨result, by simp [introMultiBounded, h, done]⟩

/-- Retrying preserves every previously successful traversal result. -/
theorem introMultiBounded_eq_of_success (fuel maxApp : Nat) (e result : Exp)
    (success : introMultiFuel fuel maxApp e = some result) :
    introMultiBounded fuel maxApp e = some result := by
  simp [introMultiBounded, success]

/-- Whole-program multi-argument introduction cannot exhaust traversal fuel. -/
theorem compileFuel_succeeds (fuel : Nat) (enabled : Bool) (maxApp : Nat) (es : List Exp) :
    ∃ result, compileFuel fuel enabled maxApp es = some result := by
  cases enabled with
  | false => exact ⟨_, rfl⟩
  | true =>
    obtain ⟨result, h⟩ := mapM_succeeds es (introMultiBounded fuel maxApp) (by
      intro e _; exact introMultiBounded_succeeds fuel maxApp e)
    exact ⟨result, by simpa [compileFuel] using h⟩

end Flapjack.Compiler.Backend.ClosMti
