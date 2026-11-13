module

public import Flapjack.Compiler.Backend.ClosKnown.Merge
public import Flapjack.Misc.Option
public import Flapjack.Misc.Sptree
public import Batteries.Data.List.Basic

@[expose] public section

/-! Source algebraic properties of known-closure approximation merging. -/
namespace Flapjack.Compiler.Backend.ClosKnownProps
open ClosKnown

/-- Merging with the unknown approximation yields the unknown approximation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "merge_Other"]
theorem mergeOther (a : ValApprox) :
    mergeHOL .other a = .other ∧ mergeHOL a .other = .other := by
  cases a <;> simp [mergeHOL]

/-- The impossible approximation is a right identity for merging. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "merge_Impossible"]
theorem mergeImpossible (a : ValApprox) : mergeHOL a .impossible = a := by
  cases a <;> simp [mergeHOL]

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

private theorem mergeListLength (xs ys : List ValApprox) :
    (mergeListHOL xs ys).length = min xs.length ys.length := by
  simp [mergeListHOL_eq_zip]

private theorem mergeListAssoc (xs ys zs : List ValApprox)
    (hxy : xs.length = ys.length) (hyz : ys.length = zs.length)
    (step : ∀ x ∈ xs, ∀ y z, mergeHOL x (mergeHOL y z) = mergeHOL (mergeHOL x y) z) :
    mergeListHOL xs (mergeListHOL ys zs) = mergeListHOL (mergeListHOL xs ys) zs := by
  induction xs generalizing ys zs with
  | nil => cases ys <;> cases zs <;> simp_all [mergeListHOL]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hxy
    | cons y ys =>
      cases zs with
      | nil => simp at hyz
      | cons z zs =>
        simp only [List.length_cons, Nat.succ.injEq] at hxy hyz
        simp only [mergeListHOL]
        rw [step x (by simp) y z, ih ys zs hxy hyz (fun v hv => step v (by simp [hv]))]

/-- Approximation merge is associative, including nested tuples. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "merge_assoc"]
theorem mergeAssoc (a b c : ValApprox) :
    mergeHOL a (mergeHOL b c) = mergeHOL (mergeHOL a b) c := by
  have all : ∀ n (a b c : ValApprox), sizeOf a < n →
      mergeHOL a (mergeHOL b c) = mergeHOL (mergeHOL a b) c := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b c bound
      cases a <;> cases b <;> cases c <;> simp [mergeHOL] at * <;>
        repeat' first | split | simp_all [mergeHOL, beq_iff_eq, mergeListLength] | omega
      apply mergeListAssoc
      · omega
      · omega
      · intro x member y z
        have small := List.sizeOf_lt_of_mem member
        exact ih (sizeOf x + 1) (by omega) x y z (by omega)
  exact all (sizeOf a + 1) a b c (by omega)

private theorem mergeListIdem (xs : List ValApprox)
    (step : ∀ x ∈ xs, mergeHOL x x = x) : mergeListHOL xs xs = xs := by
  induction xs with
  | nil => simp [mergeListHOL]
  | cons x xs ih =>
    simp only [mergeListHOL]
    rw [step x (by simp), ih (fun y hy => step y (by simp [hy]))]

/-- Merging an approximation with itself leaves it unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "merge_idem"]
theorem mergeIdem (a : ValApprox) : mergeHOL a a = a := by
  have all : ∀ n (a : ValApprox), sizeOf a < n → mergeHOL a a = a := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a bound
      cases a <;> simp only [mergeHOL, beq_self_eq_true, Bool.true_and, ↓reduceIte]
      case tuple tag xs =>
        congr 1
        apply mergeListIdem
        intro child member
        have small := List.sizeOf_lt_of_mem member
        have childBound : sizeOf child + 1 < n := by
          simp only [ValApprox.tuple.sizeOf_spec] at bound
          omega
        exact ih (sizeOf child + 1) childBound child (by omega)
  exact all (sizeOf a + 1) a (by omega)

/-- An approximation is below another when merging yields the latter. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_def"]
def subapprox (a1 a2 : ValApprox) : Prop := mergeHOL a1 a2 = a2

/-- Every approximation is below itself. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_refl"]
theorem subapproxRefl (a : ValApprox) : subapprox a a := mergeIdem a

/-- Approximation ordering is transitive. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_trans"]
theorem subapproxTrans (a1 a2 a3 : ValApprox)
    (h : subapprox a1 a2 ∧ subapprox a2 a3) : subapprox a1 a3 := by
  obtain ⟨h1, h2⟩ := h
  unfold subapprox at *
  calc
    mergeHOL a1 a3 = mergeHOL a1 (mergeHOL a2 a3) := by rw [h2]
    _ = mergeHOL (mergeHOL a1 a2) a3 := mergeAssoc _ _ _
    _ = a3 := by rw [h1, h2]

/-- Each operand is below the merge in either argument order. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_merge"]
theorem subapproxMerge (a b : ValApprox) :
    subapprox a (mergeHOL a b) ∧ subapprox a (mergeHOL b a) := by
  have first : subapprox a (mergeHOL a b) := by
    unfold subapprox
    rw [mergeAssoc, mergeIdem]
  exact ⟨first, by simpa [mergeComm b a] using first⟩

/-- Unknown is the greatest approximation in the source ordering. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_Other"]
theorem subapproxOther (a : ValApprox) :
    (subapprox .other a ↔ a = .other) ∧ subapprox a .other := by
  simp [subapprox, (mergeOther a).1, (mergeOther a).2, eq_comm]

/-- Impossible is the least approximation in the source ordering. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_Impossible"]
theorem subapproxImpossible (a : ValApprox) :
    (subapprox a .impossible ↔ a = .impossible) ∧ subapprox .impossible a := by
  simp [subapprox, mergeImpossible, mergeHOL]

/-- Integer approximations have the original lower and upper bounds. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_Int"]
theorem subapproxInt (a : ValApprox) (i : Int) :
    (subapprox a (.int i) ↔ a = .int i ∨ a = .impossible) ∧
      (subapprox (.int i) a ↔ a = .int i ∨ a = .other) := by
  cases a <;> simp [subapprox, mergeHOL, beq_iff_eq]
  case int j =>
    by_cases h : j = i
    · subst j; simp
    · have reverse : i ≠ j := Ne.symm h
      simp [h, reverse]

/-- Non-inlineable closures have the original lower and upper bounds. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_ClosNoInline"]
theorem subapproxClosNoInline (a : ValApprox) (m n : Nat) :
    (subapprox a (.closNoInline m n) ↔ a = .closNoInline m n ∨ a = .impossible) ∧
      (subapprox (.closNoInline m n) a ↔ a = .closNoInline m n ∨ a = .other) := by
  cases a <;> simp [subapprox, mergeHOL, beq_iff_eq]
  case closNoInline x y =>
    by_cases hm : x = m <;> by_cases hn : y = n <;> simp [hm, hn, Ne.symm]

/-- Inlineable closures have the original lower and upper bounds. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_Clos"]
theorem subapproxClos (a : ValApprox) (m n : Nat) (e : ClosLang.Exp) (size : Nat) :
    (subapprox a (.clos m n e size) ↔ a = .clos m n e size ∨ a = .impossible) ∧
      (subapprox (.clos m n e size) a ↔ a = .clos m n e size ∨ a = .other) := by
  cases a <;> simp [subapprox, mergeHOL, beq_iff_eq]
  case clos x y body count =>
    by_cases hm : x = m <;> by_cases hn : y = n <;> by_cases he : body = e <;>
      by_cases hs : count = size <;> simp [hm, hn, he, hs, Ne.symm]

private theorem mergeList_eq_right_iff (xs ys : List ValApprox) :
    (xs.length = ys.length ∧ mergeListHOL xs ys = ys) ↔
      List.Forall₂ subapprox xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [mergeListHOL]
    | cons y ys => simp only [List.length_nil, List.length_cons, Nat.zero_ne_add_one, false_and, false_iff]; intro h; cases h
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_cons, List.length_nil, Nat.add_one_ne_zero, false_and, false_iff]; intro h; cases h
    | cons y ys => simp [mergeListHOL, List.forall₂_cons, subapprox, ← ih, and_left_comm]

/-- Tuple approximations are ordered elementwise when their tags agree. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "subapprox_Tuple"]
theorem subapproxTuple (tag1 : Nat) (xs : List ValApprox) (tag2 : Nat) (ys : List ValApprox) :
    subapprox (.tuple tag1 xs) (.tuple tag2 ys) ↔
      tag1 = tag2 ∧ List.Forall₂ subapprox xs ys := by
  have listEq := mergeList_eq_right_iff xs ys
  by_cases len : xs.length = ys.length <;> by_cases tag : tag1 = tag2 <;>
    simp [subapprox, mergeHOL, len, tag, beq_iff_eq] at *
  all_goals assumption

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

/-- Every approximation tree is better defined than itself. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "better_definedg_refl"]
theorem betterDefinedGRefl (g : Spt ValApprox) : betterDefinedG g g := by
  intro key member
  exact ⟨member, subapproxRefl _⟩

/-- Better-defined global approximations compose. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "better_definedg_trans"]
theorem betterDefinedGTrans (g1 g2 g3 : Spt ValApprox)
    (h : betterDefinedG g1 g2 ∧ betterDefinedG g2 g3) : betterDefinedG g1 g3 := by
  intro k member
  obtain ⟨middle, first⟩ := h.1 k member
  obtain ⟨last, second⟩ := h.2 k middle
  exact ⟨last, subapproxTrans _ _ _ ⟨first, second⟩⟩

end Flapjack.Compiler.Backend.ClosKnownProps
