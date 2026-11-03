import Flapjack.Compiler.Backend.Semantics.ClosSem

/-! Symmetry of the source closure-value equality. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Closure equality and its list comparison are symmetric. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_eq_sym"]
theorem doEqSym :
    (∀ x y : Value, doEq x y = doEq y x) ∧
    (∀ xs ys : List Value, doEqList xs ys = doEqList ys xs) := by
  have all : ∀ n : Nat,
      (∀ x y : Value, sizeOf x < n → doEq x y = doEq y x) ∧
      (∀ xs ys : List Value, sizeOf xs < n → doEqList xs ys = doEqList ys xs) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      constructor
      · intro x y bound
        cases x <;> cases y <;> simp only [doEq]
        case block.block tag xs tag' ys =>
          have smaller : sizeOf xs + 1 < n := by simp only [Value.block.sizeOf_spec] at bound; omega
          have sub := (ih (sizeOf xs + 1) smaller).2 xs ys (by omega)
          by_cases h : tag = tag' ∧ xs.length = ys.length
          · have hr : tag' = tag ∧ ys.length = xs.length := ⟨h.1.symm, h.2.symm⟩
            rw [if_pos h, if_pos hr, sub]
          · have hr : ¬(tag' = tag ∧ ys.length = xs.length) := by
              intro rev
              exact h ⟨rev.1.symm, rev.2.symm⟩
            rw [if_neg h, if_neg hr]
        all_goals first | (congr 2 <;> exact propext eq_comm) | (simp only [Bool.and_comm, eq_comm])
      · intro xs ys bound
        cases xs with
        | nil => cases ys <;> simp only [doEqList]
        | cons x xs =>
          cases ys with
          | nil => simp only [doEqList]
          | cons y ys =>
            have smallerHead : sizeOf x + 1 < n := by simp only [List.cons.sizeOf_spec] at bound; omega
            have smallerTail : sizeOf xs + 1 < n := by simp only [List.cons.sizeOf_spec] at bound; omega
            have head := (ih (sizeOf x + 1) smallerHead).1 x y (by omega)
            have tail := (ih (sizeOf xs + 1) smallerTail).2 xs ys (by omega)
            simp only [doEqList, head, tail]
  constructor
  · intro x y; exact (all (sizeOf x + 1)).1 x y (by omega)
  · intro xs ys; exact (all (sizeOf xs + 1)).2 xs ys (by omega)

end Flapjack.Compiler.Backend.ClosProps
