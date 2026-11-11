module

public import Flapjack.Compiler.Backend.ClosKnown.Merge
public import Flapjack.Misc.Option
public import Flapjack.Misc.Sptree

@[expose] public section

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
        rw [beqSym loc' loc, beqSym arity' arity]
        split <;> simp_all [Bool.and_eq_true, beq_iff_eq]
      case clos.clos loc arity body size loc' arity' body' size' =>
        rw [beqSym loc' loc, beqSym arity' arity, beqSym body' body, beqSym size' size]
        split <;> simp_all [Bool.and_eq_true, beq_iff_eq]
      case int.int i j =>
        rw [beqSym j i]
        split <;> simp_all [beq_iff_eq]
      case tuple.tuple tag xs tag' ys =>
        rw [beqSym tag' tag, beqSym ys.length xs.length]
        split
        · rename_i test
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp test
          simp only [beq_iff_eq] at h1 h2
          subst tag'
          congr 1
          refine mergeListComm xs ys h1 (fun child member otherApprox => ?_)
          have small := List.sizeOf_lt_of_mem member
          have childBound : sizeOf child + 1 < n := by
            simp only [ValApprox.tuple.sizeOf_spec] at bound
            omega
          exact ih (sizeOf child + 1) childBound child otherApprox (by omega)
        · rfl
  exact all (sizeOf a + 1) a b (by omega)

/-- An approximation is below another when merging yields the latter. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_def"]
def subapprox (a1 a2 : ValApprox) : Prop := mergeHOL a1 a2 = a2

/-- Approximation ordering is antisymmetric. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_antisym"]
theorem subapproxAntisym (a1 a2 : ValApprox)
    (h : subapprox a1 a2 ∧ subapprox a2 a1) : a1 = a2 := by
  obtain ⟨left, right⟩ := h
  unfold subapprox at left right
  rw [mergeComm] at left
  exact right.symm.trans left

/-- Each present approximation is preserved or becomes more general. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "better_definedg_def"]
noncomputable def betterDefinedG (g1 g2 : Spt ValApprox) : Prop :=
  ∀ k, sptMem k g1 → sptMem k g2 ∧
    subapprox (@Flapjack.holThe ValApprox ⟨.other⟩ (sptLookup k g1))
      (@Flapjack.holThe ValApprox ⟨.other⟩ (sptLookup k g2))

end Flapjack.Compiler.Backend.ClosKnownProps
