import Flapjack.Misc.BytesInMemory
import Mathlib.Data.Set.Basic
import Lean.Elab.Tactic.Omega

/-! Native asmProps stride PC sets and encoded-byte domain coverage. -/
namespace Flapjack.Compiler.Encoders.AsmProps
open Flapjack

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "all_pcs_def"
  (words_as_type_indexed_bitvec)]
def allPcs {width : Nat} [NeZero width] (n : Nat) (address : BitVec width)
    (alignment : Nat) : Set (BitVec width) :=
  if n = 0 then ∅ else
    {address} ∪ allPcs (n - 2 ^ alignment)
      (address + BitVec.ofNat width (2 ^ alignment)) alignment
termination_by n
decreasing_by
  have h : 0 < 2 ^ alignment := Nat.pow_pos (by decide)
  omega

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "all_pcs_thm"
  (words_as_type_indexed_bitvec)]
theorem allPcs_eq {width : Nat} [NeZero width] (n : Nat)
    (address : BitVec width) (alignment : Nat) :
    allPcs n address alignment =
      {x | ∃ i : Nat, i * 2 ^ alignment < n ∧
        x = address + BitVec.ofNat width (i * 2 ^ alignment)} := by
  induction n using Nat.strong_induction_on generalizing address with
  | h n ih =>
    have hp : 0 < 2 ^ alignment := Nat.pow_pos (by decide)
    by_cases hz : n = 0
    · subst n
      simp [allPcs]
    · have hl : n - 2 ^ alignment < n := by omega
      rw [allPcs, if_neg hz, ih _ hl]
      ext x
      change (x = address ∨ ∃ i, i * 2 ^ alignment < n - 2 ^ alignment ∧
        x = address + BitVec.ofNat width (2 ^ alignment) + BitVec.ofNat width (i * 2 ^ alignment)) ↔ _
      constructor
      · rintro (rfl | ⟨i, hi, hx⟩)
        · exact ⟨0, by simp; omega, by simp⟩
        · refine ⟨i + 1, ?_, ?_⟩
          · rw [Nat.add_mul]
            simp only [Nat.one_mul]
            omega
          · rw [hx, Nat.add_mul, Nat.one_mul, Nat.add_comm (i * 2 ^ alignment)]
            simp [BitVec.ofNat_add, BitVec.add_assoc]
      · rintro ⟨i, hi, hx⟩
        cases i with
        | zero => left; simpa using hx
        | succ i =>
          right
          refine ⟨i, ?_, ?_⟩
          · rw [Nat.succ_mul] at hi
            omega
          · rw [hx, Nat.succ_mul, Nat.add_comm (i * 2 ^ alignment)]
            simp [BitVec.ofNat_add, BitVec.add_assoc]

/-- Local induction infrastructure for the tagged domain-coverage theorem;
not a separately claimed HOL declaration. -/
private theorem byteOffsetInDomain {width : Nat} [NeZero width]
    (xs : List (BitVec 8)) (address : BitVec width)
    (memory : BitVec width → BitVec 8) (domain : BitVec width → Prop)
    (h : bytesInMemoryHOL address xs memory domain)
    (offset : Nat) (bound : offset < xs.length) :
    domain (address + BitVec.ofNat width offset) := by
  induction xs generalizing address offset with
  | nil => simp at bound
  | cons b xs ih =>
    cases offset with
    | zero => simpa using h.2.1
    | succ offset =>
      have ho : offset < xs.length := by simpa using bound
      have hd := ih (address + 1) h.2.2 offset ho
      have he : (address + 1) + BitVec.ofNat width offset =
          address + BitVec.ofNat width (offset + 1) := by
        rw [BitVec.ofNat_add, BitVec.add_assoc]
        exact congrArg (address + ·) (BitVec.add_comm _ _)
      exact he ▸ hd

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "bytes_in_memory_all_pcs"
  (words_as_type_indexed_bitvec)]
theorem bytesInMemory_allPcs {width : Nat} [NeZero width]
    (xs : List (BitVec 8)) (address : BitVec width)
    (memory : BitVec width → BitVec 8) (domain : BitVec width → Prop)
    (alignment : Nat) :
    bytesInMemoryHOL address xs memory domain →
      allPcs xs.length address alignment ⊆ domain := by
  intro h x hx
  rw [allPcs_eq] at hx
  rcases hx with ⟨i, hi, rfl⟩
  exact byteOffsetInDomain xs address memory domain h (i * 2 ^ alignment) hi

end Flapjack.Compiler.Encoders.AsmProps
