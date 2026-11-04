import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare

/-! Bounds comparisons for 64-bit immediate and heap-backed numbers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Rotating a small integer gives the original nonnegative index for bounds comparisons. -/
theorem smallnum_rotateRight_bounds64 (i : Int) (n : Nat) (small : smallInt 64 i) (bound : n < 2305843009213693952) :
    (((smallnum i : BitVec 64).rotateRight 2).toNat < n ↔ 0 ≤ i ∧ i < (n : Int)) := by
  have interval : -(2305843009213693952 : Int) ≤ i ∧ i < 2305843009213693952 := by
    simpa [smallInt] using small
  have vInt : (BitVec.ofInt 64 i).toInt = i := by
    apply BitVec.toInt_ofInt_eq_self <;> norm_num <;> omega
  have nNat : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have nInt : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [← BitVec.ofInt_natCast, BitVec.toInt_ofInt_eq_self] <;> norm_num; omega
  have encode : (smallnum i : BitVec 64) = (BitVec.ofInt 64 i <<< 2) := by
    rw [Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.smallnum_i2w, BitVec.ofInt_mul]
    simp only [show BitVec.ofInt 64 4 = 4 by rfl]
    bv_decide
  have b : (BitVec.ofNat 64 n).ult 2305843009213693952 = true := by
    simp [BitVec.ult_eq_decide, nNat, bound]
  have l : (BitVec.ofInt 64 i).slt 16140901064495857664 = false := by
    simp [BitVec.slt_eq_decide, vInt, not_lt.mpr interval.1]
  have u : (BitVec.ofInt 64 i).slt 2305843009213693952 = true := by
    simp [BitVec.slt_eq_decide, vInt, interval.2]
  have fact : ((BitVec.ofInt 64 i <<< 2).rotateRight 2).ult (BitVec.ofNat 64 n) =
      (!(BitVec.ofInt 64 i).slt 0 && (BitVec.ofInt 64 i).slt (BitVec.ofNat 64 n)) := by bv_decide
  rw [← encode] at fact
  have final := congrArg (fun x : Bool => x = true) fact
  simpa [BitVec.ult_eq_decide, BitVec.slt_eq_decide, vInt, nNat, nInt] using final
/-- A heap pointer rotates its marker bit above any valid bound. -/
theorem pointer_rotateRight_bounds64 (v n : BitVec 64) (bit : v.getLsbD 0 = true)
    (bound : n.ult 2305843009213693952 = true) :
    (v.rotateRight 2).ult n = false := by
  bv_decide

/-- The 64-bit strict bounds comparison for a related numeric value. This is
Flapjack-side infrastructure toward the source's width-polymorphic strict and
non-strict memory relation theorem. -/
theorem memoryRel_numberBounds64 (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (i : Int) (word : BitVec 64) (vars : List (Value × WordLocW 64)) (n : Nat)
    (related : memoryRel conf bigEndian next refs space store memory domain ((.number i, .word word) :: vars))
    (bound : n < 2305843009213693952) :
    ((word.rotateRight 2).toNat < n ↔ 0 ≤ i ∧ i < (n : Int)) := by
  by_cases small : smallInt 64 i
  · have encoded := memoryRel_numberImp conf bigEndian next refs space store memory domain i (.word word) vars
      ⟨Or.inr rfl, small, related⟩
    have eq := WordLocW.word.inj encoded
    rw [eq]
    exact smallnum_rotateRight_bounds64 i n small bound
  · obtain ⟨w, equal, marker⟩ := memoryRel_anyNumberImp conf bigEndian next refs space store memory domain
      i (.word word) vars ⟨Or.inr rfl, related⟩
    have eq : word = w := WordLocW.word.inj equal
    subst w
    have low : word.getLsbD 0 = true := marker.mpr small
    have nNat : (BitVec.ofNat 64 n).toNat = n := by
      simp only [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      norm_num
      omega
    have b : (BitVec.ofNat 64 n).ult 2305843009213693952 = true := by
      simp [BitVec.ult_eq_decide, nNat, bound]
    have notBelow := pointer_rotateRight_bounds64 word (BitVec.ofNat 64 n) low b
    have target : ¬ (word.rotateRight 2).toNat < n := by
      simpa [BitVec.ult_eq_decide, nNat] using notBelow
    have source : ¬ (0 ≤ i ∧ i < (n : Int)) := by
      intro h
      apply small
      norm_num [smallInt]
      omega
    exact iff_of_false target source

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
