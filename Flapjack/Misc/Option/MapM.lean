module

public import Batteries.Data.List.Basic

@[expose] public section

/-! Flapjack infrastructure for successful option-valued list traversals. -/
namespace Flapjack

/-- Flapjack proof infrastructure: successful option traversals relate their
source and target elements pointwise. -/
theorem mapM_rel {A B : Type} (f : A → Option B) (r : A → B → Prop)
    (pointwise : ∀ a b, f a = some b → r a b)
    (source : List A) (target : List B) (run : source.mapM f = some target) :
    List.Forall₂ r source target := by
  induction source generalizing target with
  | nil => simp at run; subst target; exact .nil
  | cons first rest ih =>
    cases head : f first with
    | none => simp [List.mapM_cons, head] at run
    | some next =>
      cases tail : rest.mapM f with
      | none => simp [List.mapM_cons, head, tail] at run
      | some nextRest =>
        have equal : next :: nextRest = target := by simpa [List.mapM_cons, head, tail] using run
        subst target
        exact .cons (pointwise first next head) (ih nextRest tail)

/-- A successful traversal agreeing pointwise with a total function is its list map. -/
theorem mapM_eq_map {α β : Type} (visit : α → Option β) (f : α → β)
    (correct : ∀ x y, visit x = some y → y = f x) (xs : List α) (ys : List β)
    (run : xs.mapM visit = some ys) : ys = xs.map f := by
  have rel := mapM_rel visit (fun x y => y = f x) correct xs ys run
  clear run
  induction rel with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, first, ih]

/-- Mapping an option-valued function succeeds when it succeeds on every
member of the input list. -/
theorem mapM_succeeds {α β : Type} (xs : List α) (f : α → Option β)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (by intro z hz; exact h z (by simp [hz]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

end Flapjack
