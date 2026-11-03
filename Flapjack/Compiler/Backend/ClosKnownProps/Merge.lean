import Flapjack.Compiler.Backend.ClosKnown.Merge

/-! Source algebraic properties of known-closure approximation merging. -/
namespace Flapjack.Compiler.Backend.ClosKnownProps
open ClosKnown

private theorem mergeListComm (xs ys : List ValApprox) (len : xs.length = ys.length)
    (step : ∀ x ∈ xs, ∀ y, mergeHOL x y = mergeHOL y x) :
    mergeListHOL xs ys = mergeListHOL ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [mergeListHOL]
  | cons x xs ih =>
    cases ys with
    | nil => simp at len
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at len
      simp only [mergeListHOL]
      rw [step x (by simp) y, ih ys len (fun z hz => step z (by simp [hz]))]

private theorem beqSym {α : Type} [BEq α] [LawfulBEq α] (x y : α) : (x == y) = (y == x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact eq_comm

/-- Approximation merge is commutative. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "merge_comm"]
theorem mergeComm (a b : ValApprox) : mergeHOL a b = mergeHOL b a := by
  have all : ∀ n (a b : ValApprox), sizeOf a < n → mergeHOL a b = mergeHOL b a := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b bound
      cases a <;> cases b <;> simp only [mergeHOL]
      case closNoInline.closNoInline loc arity loc' arity' =>
        simp only [Bool.and_eq_true, beq_iff_eq]
        by_cases h : loc = loc' ∧ arity = arity'
        · have rev : loc' = loc ∧ arity' = arity := ⟨h.1.symm, h.2.symm⟩
          rw [if_pos h, if_pos rev]
          rcases h with ⟨rfl, rfl⟩
          rfl
        · have rev : ¬(loc' = loc ∧ arity' = arity) := by
            intro r; exact h ⟨r.1.symm, r.2.symm⟩
          rw [if_neg h, if_neg rev]
      case clos.clos loc arity body size loc' arity' body' size' =>
        rw [← beqSym loc loc', ← beqSym arity arity', ← beqSym body body', ← beqSym size size']
        split
        · rename_i test
          obtain ⟨h123, h4⟩ := Bool.and_eq_true_iff.mp test
          obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h123
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
          have e1 := beq_iff_eq.mp h1
          have e2 := beq_iff_eq.mp h2
          have e3 := beq_iff_eq.mp h3
          have e4 := beq_iff_eq.mp h4
          subst loc'; subst arity'; subst body'; subst size'
          rfl
        · rfl
      case int.int i j =>
        simp only [beq_iff_eq]
        by_cases h : i = j
        · subst j; rfl
        · have rev : j ≠ i := Ne.symm h
          rw [if_neg h, if_neg rev]
      case tuple.tuple tag xs tag' ys =>
        simp only [Bool.and_eq_true, beq_iff_eq]
        by_cases h : xs.length = ys.length ∧ tag = tag'
        · have rev : ys.length = xs.length ∧ tag' = tag := ⟨h.1.symm, h.2.symm⟩
          rw [if_pos h, if_pos rev]
          have tagEq := h.2
          subst tag'
          congr 1
          apply mergeListComm xs ys h.1
          intro child member otherApprox
          have small := List.sizeOf_lt_of_mem member
          have childBound : sizeOf child + 1 < n := by
            simp only [ValApprox.tuple.sizeOf_spec] at bound
            omega
          exact ih (sizeOf child + 1) childBound child otherApprox (by omega)
        · have rev : ¬(ys.length = xs.length ∧ tag' = tag) := by
            intro h'
            exact h ⟨h'.1.symm, h'.2.symm⟩
          rw [if_neg h, if_neg rev]
  exact all (sizeOf a + 1) a b (by omega)

end Flapjack.Compiler.Backend.ClosKnownProps
