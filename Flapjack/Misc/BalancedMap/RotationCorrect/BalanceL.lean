import Flapjack.FiniteMap.Comparison
import Flapjack.Misc.BalancedMap.Rotations
import Flapjack.Misc.BalancedMap.RotationAux
import Flapjack.Misc.BalancedMap.StructuralSize
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

/-- Constructor constraint derived from the literal invariant. Flapjack proof
infrastructure, with no separate HOL declaration: it adds no theorem premise. -/
private theorem zeroSizeTip {κ ν : Type} (cmp : κ → κ → Ordering)
    (tree : Map κ ν) (hinv : invariant cmp tree) (hzero : size tree = 0) :
    tree = .tip := by
  have hs := structureSizeThm cmp tree hinv
  cases tree with
  | tip => rfl
  | bin n key value left right =>
    change n = 1 + structureSize left + structureSize right at hs
    change n = 0 at hzero
    omega

/-- Literal invariant normalization, retaining recursive invariants and key
order; only cached sizes are rewritten to the sizes of valid children. -/
private theorem binFacts {κ ν : Type} (cmp : κ → κ → Ordering)
    (n : Nat) (key : κ) (value : ν) (left right : Map κ ν)
    (hinv : invariant cmp (.bin n key value left right)) :
    n = 1 + size left + size right ∧ balanced (size left) (size right) ∧
    invariant cmp left ∧ invariant cmp right := by
  have hl := structureSizeThm cmp left hinv.2.2.2.2.1
  have hr := structureSizeThm cmp right hinv.2.2.2.2.2
  exact ⟨by rw [hl, hr]; exact hinv.1,
    hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩

/-- An invariant tree with one empty child forces the other child's cached
size to at most one. This discharges the source small-constructor branches. -/
private theorem balancedZero (n : Nat) (h : balanced 0 n) : n ≤ 1 := by
  simp only [balanced, Nat.zero_add, Nat.max_eq_right (Nat.zero_le n),
    Nat.min_eq_left (Nat.zero_le n), Nat.mul_zero] at h
  omega

/-- Every invariant one-node tree has both children empty; derived rather
than assumed in the full balancing equivalence. -/
private theorem singletonChildren {κ ν : Type} (cmp : κ → κ → Ordering)
    (n : Nat) (key : κ) (value : ν) (left right : Map κ ν)
    (hinv : invariant cmp (.bin n key value left right)) (hsmall : n ≤ 1) :
    n = 1 ∧ left = .tip ∧ right = .tip := by
  have hf := binFacts cmp n key value left right hinv
  have hl0 : size left = 0 := by omega
  have hr0 : size right = 0 := by omega
  exact ⟨by omega, zeroSizeTip cmp left hf.2.2.1 hl0,
    zeroSizeTip cmp right hf.2.2.2 hr0⟩

/-- Symmetric zero-child bound for literal balance predicate; local proof
infrastructure, not a separate HOL declaration. -/
private theorem balancedZeroRight (n : Nat) (h : balanced n 0) : n ≤ 1 := by
  simp only [balanced, Nat.add_zero, Nat.max_eq_left (Nat.zero_le n),
    Nat.min_eq_right (Nat.zero_le n), Nat.mul_zero] at h
  omega

/-- Entire original production/proof left-balancing equality. Every small
constructor restriction is derived from the input invariants. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanceL_balL"]
theorem balanceLBalL {κ ν : Type} (key : κ) (value : ν) (left right : Map κ ν)
    (cmp : κ → κ → Ordering)
    (h : goodCmp cmp ∧ invariant cmp left ∧ invariant cmp right) :
    balanceL key value left right = balL key value left right := by
  obtain ⟨_hgood, hl, hr⟩ := h
  cases left with
  | tip =>
    cases right with
    | tip => rfl
    | bin n root rootValue first middle =>
      simp [balanceL, balL, size, delta, Nat.add_comm]
  | bin n root rootValue first middle =>
    have hf := binFacts cmp n root rootValue first middle hl
    cases right with
    | tip =>
      cases first with
      | tip =>
        cases middle with
        | tip =>
          have hn : n = 1 := by simpa [size] using hf.1
          subst n
          rfl
        | bin m pivot pivotValue second third =>
          have hm : m ≤ 1 := balancedZero m hf.2.1
          obtain ⟨hm1, hs, ht⟩ := singletonChildren cmp m pivot pivotValue second third hf.2.2.2 hm
          subst m
          subst second
          subst third
          have hn : n = 2 := by simpa [size] using hf.1
          subst n
          simp [balanceL, balL, rotateR, doubleRDef, size, delta, ratio, bin]
      | bin m pivot pivotValue second third =>
        cases middle with
        | tip =>
          have hm : m ≤ 1 := balancedZeroRight m hf.2.1
          have hm1 := (singletonChildren cmp m pivot pivotValue second third hf.2.2.1 hm).1
          subst m
          have hn : n = 2 := by simpa [size] using hf.1
          subst n
          simp [balanceL, balL, rotateR, singleRDef, size, delta, ratio, bin]
        | bin m0 pivot0 pivotValue0 second0 third0 =>
          have hn : n = 1 + m + m0 := by simpa [size] using hf.1
          have hmpos : 0 < m := by
            have hfm := binFacts cmp m pivot pivotValue second third hf.2.2.1
            omega
          have hnlarge : ¬ (n ≤ 1) := by omega
          have hnheavy : n > 0 := by omega
          simp only [balanceL, balL, rotateR, size, Nat.add_zero, Nat.mul_zero]
          simp only [hnlarge, hnheavy, if_false, if_true]
          have hm0 : m0 = 1 + size second0 + size third0 :=
            (binFacts cmp m0 pivot0 pivotValue0 second0 third0 hf.2.2.2).1
          by_cases hratio : m0 < ratio * m
          · simp only [hratio, if_pos, singleRDef]
            simp [bin, size, hn, Nat.add_comm, Nat.add_left_comm]
          · simp only [hratio, doubleRDef]
            simp [bin, size, hn, hm0, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    | bin rn rkey rvalue rl rr =>
      have rpositive : 0 < rn := by
        have hrf := binFacts cmp rn rkey rvalue rl rr hr
        omega
      have npositive : 0 < n := by omega
      have hlarge : ¬ (n + rn ≤ 1) := by omega
      by_cases hheavy : n > delta * rn
      · cases first with
        | tip =>
          have hm : size middle ≤ 1 := balancedZero _ hf.2.1
          have hn : n = 1 + 0 + size middle := hf.1
          simp only [delta] at hheavy
          omega
        | bin m pivot pivotValue second third =>
          cases middle with
          | tip =>
            have hm : m ≤ 1 := balancedZeroRight m hf.2.1
            have hn : n = 1 + m + 0 := hf.1
            simp only [delta] at hheavy
            omega
          | bin m0 pivot0 pivotValue0 second0 third0 =>
            have hn : n = 1 + m + m0 := hf.1
            have hm0 : m0 = 1 + size second0 + size third0 :=
              (binFacts cmp m0 pivot0 pivotValue0 second0 third0 hf.2.2.2).1
            by_cases hratio : m0 < ratio * m
            · simp only [balanceL, balL, rotateR, size]
              simp only [hlarge, hheavy, hratio, if_false, if_true, singleRDef]
              simp [bin, size, hn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            · simp only [balanceL, balL, rotateR, size]
              simp only [hlarge, hheavy, hratio, if_false, if_true, doubleRDef]
              simp [bin, size, hn, hm0, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · cases first <;> cases middle <;>
          simp [balanceL, balL, size, hlarge, hheavy,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Flapjack.Misc.BalancedMap
