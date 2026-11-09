module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Depth.Limit
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockTests
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Resource bounds for related source values. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- Each member's depth is bounded by the maximum of the list. -/
private theorem depth_le_max (x : Value) (xs : List Value) (member : x ∈ xs) :
    vDepth x ≤ vDepthMax xs := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    simp only [List.mem_cons] at member
    simp only [vDepthMax]
    rcases member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- A pointwise bound gives a bound on the sum of list elements. -/
private theorem sum_le_length_mul (xs : List Nat) (bound : Nat)
    (each : ∀ x, x ∈ xs → x ≤ bound) : xs.sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    have head := each x (by simp)
    have tail := ih (fun y hy => each y (by simp [hy]))
    omega

/-- A related value's structural size is bounded exponentially by its depth. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_depth_size_limit"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_depthSizeLimit {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v : Value) (location : WordLocW width) (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((v, location) :: vars) ∧
      goodDimindex width → valueBlockSize v ≤ (2 ^ width) ^ (vDepth v + 1) := by
  generalize eqSize : valueBlockSize v = n
  induction n using Nat.strong_induction_on generalizing v location vars with
  | h n ih =>
    rintro ⟨rel, good⟩
    rw [← eqSize]
    cases v with
    | number i => simpa only [valueBlockSize, vDepth, Nat.zero_add, pow_one] using (Nat.succ_le_iff.mpr (Nat.two_pow_pos width))
    | word64 w => simpa only [valueBlockSize, vDepth, Nat.zero_add, pow_one] using (Nat.succ_le_iff.mpr (Nat.two_pow_pos width))
    | codePtr c => simpa only [valueBlockSize, vDepth, Nat.zero_add, pow_one] using (Nat.succ_le_iff.mpr (Nat.two_pow_pos width))
    | refPtr b i => simpa only [valueBlockSize, vDepth, Nat.zero_add, pow_one] using (Nat.succ_le_iff.mpr (Nat.two_pow_pos width))
    | block stamp tag xs =>
      have tagBound := memoryRel_tagLimit conf be next refs space store memory domain
        stamp tag xs location vars ⟨rel, good⟩
      by_cases empty : xs = []
      · subst xs
        simp only [valueBlockSize, List.map_nil, List.sum_nil, List.length_nil, vDepth, vDepthMax,
          ↓reduceIte, Nat.zero_add, Nat.add_zero, pow_one]
        rcases good with h | h <;> subst width <;> norm_num at tagBound ⊢ <;> omega
      · obtain ⟨w, locEq, info⟩ := memoryRel_blockImp conf be next refs space store memory domain
          stamp tag xs location vars ⟨rel, good⟩
        simp only [empty, ↓reduceIte] at info
        obtain ⟨addr, header, _, _, _, _, _, _, _, lengthBound, _, _⟩ := info
        let base := 2 ^ width
        let exponent := vDepthMax xs + 1
        have basePos : 0 < base := Nat.two_pow_pos width
        have powerPos : 0 < base ^ exponent := pow_pos basePos _
        have each : ∀ x, x ∈ xs → valueBlockSize x ≤ base ^ exponent := by
          intro x member
          have less : valueBlockSize x < n := by
            rw [← eqSize]
            exact child_size_lt x stamp tag xs member
          obtain ⟨before, after, xsEq⟩ := List.append_of_mem member
          have indexBound : before.length < xs.length := by rw [xsEq]; simp
          obtain ⟨cw, ca, off, _, _, _, _, childRel⟩ :=
            memoryRel_blockMem conf be next refs space store memory domain stamp tag xs location vars
              before.length indexBound ⟨rel, good⟩
          have getEq : xs[before.length] = x := by simp [xsEq]
          rw [getEq] at childRel
          have childBound := ih (valueBlockSize x) less x (memory (ca + off))
            ((.block stamp tag xs, location) :: vars) rfl ⟨childRel, good⟩
          exact Nat.le_trans childBound (Nat.pow_le_pow_right (by omega) (by
            dsimp [exponent]
            exact Nat.add_le_add_right (depth_le_max x xs member) 1))
        have sumBound : (xs.map valueBlockSize).sum ≤ xs.length * base ^ exponent := by
          rw [← List.length_map valueBlockSize]
          apply sum_le_length_mul
          intro size member
          obtain ⟨x, mem, rfl⟩ := List.mem_map.mp member
          exact each x mem
        have margin : 1 + tag + 2 * xs.length ≤ base := by
          dsimp [base]
          rcases good with h | h <;> subst width <;> norm_num at tagBound lengthBound ⊢ <;> omega
        have scaled : 1 + tag + xs.length ≤ (1 + tag + xs.length) * base ^ exponent := by
          nlinarith
        have product : (xs.length * base ^ exponent) + (1 + tag + xs.length) * base ^ exponent ≤
            base * base ^ exponent + xs.length * base ^ exponent := by
          nlinarith
        simp only [valueBlockSize, vDepth, empty, ↓reduceIte]
        dsimp [exponent] at *
        rw [show 1 + vDepthMax xs + 1 = (vDepthMax xs + 1) + 1 by omega, pow_succ]
        dsimp [base] at *
        nlinarith

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
