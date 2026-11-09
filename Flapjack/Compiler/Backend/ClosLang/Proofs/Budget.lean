import Flapjack.Misc.Option.MapM
import Flapjack.Compiler.Backend.ClosLang.Budget
import Flapjack.Compiler.Backend.ListFoldTotal

/-! Structural budget facts for closure-language traversals. These are
Flapjack infrastructure, not HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.ClosLang

/-- Each member is strictly smaller than the budget of its expression list. -/
theorem member_budget_lt (xs : List Exp) (e : Exp) (h : e ∈ xs) :
    expBudget e < listBudget xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [listBudget]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

/-- Each recursive function body is strictly smaller than its group budget. -/
theorem fun_member_budget_lt (fns : List (Nat × Exp)) (arity : Nat) (e : Exp)
    (h : (arity, e) ∈ fns) : expBudget e < funsBudget fns := by
  induction fns with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨n, body⟩ := p
    simp only [List.mem_cons] at h
    simp only [funsBudget]
    rcases h with same | h
    · cases same; omega
    · have := ih h; omega

/-- A successful option-valued map preserves list length. -/
theorem mapM_length {α β : Type} (xs : List α) (f : α → Option β) (ys : List β)
    (h : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; rfl
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons, hx, ht] at h
      | some tail =>
        simp [List.mapM_cons, hx, ht] at h
        subst ys
        simp [ih tail ht]

end Flapjack.Compiler.Backend.ClosLang
