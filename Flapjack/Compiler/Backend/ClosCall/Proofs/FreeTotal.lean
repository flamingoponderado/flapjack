import Flapjack.Compiler.Backend.ClosCall
import Flapjack.Compiler.Backend.ClosLang.Proofs.Budget

/-! Structural sufficiency for closure free-variable analysis. These are
Flapjack infrastructure lemmas, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang DbVars

mutual
/-- Free-variable analysis succeeds under a structural traversal bound. -/
theorem freeFuel_succeeds (fuel : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, freeFuel fuel e = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases e with
    | var t v => exact ⟨_, rfl⟩
    | ifThenElse t x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', a⟩, hx⟩ := freeFuel_succeeds fuel x bx
      obtain ⟨⟨y', b⟩, hy⟩ := freeFuel_succeeds fuel y by'
      obtain ⟨⟨z', c⟩, hz⟩ := freeFuel_succeeds fuel z bz
      exact ⟨_, by simp [freeFuel, hx, hy, hz]; rfl⟩
    | «let» t xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ys, a⟩, hy⟩ := freeListFuel_succeeds fuel xs bx
      obtain ⟨⟨body', b⟩, hb⟩ := freeFuel_succeeds fuel body bb
      exact ⟨_, by simp [freeFuel, hy, hb]; rfl⟩
    | raise t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', a⟩, hx⟩ := freeFuel_succeeds fuel x bx
      exact ⟨_, by simp [freeFuel, hx]; rfl⟩
    | tick t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', a⟩, hx⟩ := freeFuel_succeeds fuel x bx
      exact ⟨_, by simp [freeFuel, hx]; rfl⟩
    | handle t x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', a⟩, hx⟩ := freeFuel_succeeds fuel x bx
      obtain ⟨⟨y', b⟩, hy⟩ := freeFuel_succeeds fuel y by'
      exact ⟨_, by simp [freeFuel, hx, hy]; rfl⟩
    | op t op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ys, a⟩, hy⟩ := freeListFuel_succeeds fuel xs bx
      exact ⟨_, by simp [freeFuel, hy]; rfl⟩
    | call t ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ys, a⟩, hy⟩ := freeListFuel_succeeds fuel xs bx
      exact ⟨_, by simp [freeFuel, hy]; rfl⟩
    | app t loc x xs =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', a⟩, hx⟩ := freeFuel_succeeds fuel x bx
      obtain ⟨⟨ys, b⟩, hy⟩ := freeListFuel_succeeds fuel xs bs
      exact ⟨_, by simp [freeFuel, hx, hy]; rfl⟩
    | fn name loc vs arity body =>
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨body', a⟩, hb⟩ := freeFuel_succeeds fuel body bb
      exact ⟨_, by simp [freeFuel, hb]; rfl⟩
    | letrec names loc vs fns body =>
      have bf : funsBudget fns < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨fs, hf⟩ := mapM_succeeds fns (fun p => do
        let (body, free) ← freeFuel fuel p.2
        pure ((p.1, body), DbVarSet.shift (p.1 + fns.length) free)) (by
          intro p hp; obtain ⟨arity, e⟩ := p
          obtain ⟨⟨e', free⟩, he⟩ := freeFuel_succeeds fuel e (by
            have := fun_member_budget_lt fns arity e hp; omega)
          exact ⟨_, by simp [he]; rfl⟩)
      obtain ⟨⟨body', b⟩, hb⟩ := freeFuel_succeeds fuel body bb
      refine ⟨(.letrec names loc (some (varsToList (listMkUnion (fs.map Prod.snd))))
        (fs.map Prod.fst) body', mkUnion (listMkUnion (fs.map Prod.snd)) (.shift fns.length b)), ?_⟩
      simp only [freeFuel]
      change (fns.mapM (fun (p : Nat × Exp) => do
        let (body, free) ← freeFuel fuel p.2
        pure ((p.1, body), DbVarSet.shift (p.1 + fns.length) free))).bind
          (fun fs => (freeFuel fuel body).bind (fun result =>
            some (Exp.letrec names loc (some (varsToList (listMkUnion (fs.map Prod.snd))))
              (fs.map Prod.fst) result.1, mkUnion (listMkUnion (fs.map Prod.snd))
                (.shift fns.length result.2)))) = _
      rw [hf, hb]
      rfl
termination_by fuel

/-- Free-variable analysis of a list succeeds under its structural bound. -/
theorem freeListFuel_succeeds (fuel : Nat) (xs : List Exp) (bound : listBudget xs < fuel) :
    ∃ result, freeListFuel fuel xs = some result := by
  cases xs with
  | nil => cases fuel <;> exact ⟨_, rfl⟩
  | cons x xs =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
      have bxs : listBudget xs < fuel := by simp_all [listBudget] <;> omega
      obtain ⟨⟨x', a⟩, hx⟩ := freeFuel_succeeds fuel x bx
      obtain ⟨⟨xs', b⟩, hxs⟩ := freeListFuel_succeeds fuel xs bxs
      exact ⟨_, by simp [freeListFuel, hx, hxs]; rfl⟩
termination_by fuel
end

/-- The production free-variable retry cannot exhaust traversal fuel. -/
theorem freeBounded_succeeds (fuel : Nat) (e : Exp) :
    ∃ result, freeBounded fuel e = some result := by
  cases h : freeFuel fuel e with
  | some result => exact ⟨result, by simp [freeBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := freeFuel_succeeds (max fuel (expBudget e + 1)) e bound
    exact ⟨result, by simp [freeBounded, h, done]⟩

/-- Retrying preserves all previously successful free-variable results. -/
theorem freeBounded_eq_of_success (fuel : Nat) (e : Exp) (result : Exp × DbVarSet)
    (success : freeFuel fuel e = some result) : freeBounded fuel e = some result := by
  simp [freeBounded, success]

/-- Closedness checks cannot fail from free-variable traversal fuel. -/
theorem closedFuel_succeeds (fuel : Nat) (e : Exp) : ∃ result, closedFuel fuel e = some result := by
  obtain ⟨⟨e', free⟩, h⟩ := freeBounded_succeeds fuel e
  exact ⟨_, by simp [closedFuel, h]; rfl⟩

end Flapjack.Compiler.Backend.ClosCall
