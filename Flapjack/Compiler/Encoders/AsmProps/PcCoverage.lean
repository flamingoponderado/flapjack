module

public import Flapjack.Misc.BytesInMemory
public import Mathlib.Data.Set.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

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

/-- Adding one before the `j`-th byte offset is the `(j + 1)`-th byte offset.
Shared by the asmProps coverage proof and the closed machine models;
Flapjack infrastructure, no HOL original. -/
theorem addOneOffset {width : Nat} (a : BitVec width) (j : Nat) :
    (a + 1) + BitVec.ofNat width j = a + BitVec.ofNat width (j + 1) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  congr 1
  exact BitVec.add_comm _ _

/-- The `j`-th byte of a byte list in memory is the `j`-th byte of the list,
for every `j` below the length.  Shared with the closed machine models;
Flapjack infrastructure, no HOL original. -/
theorem bytesInMemoryHOL_get {width : Nat} [NeZero width]
    {a : BitVec width} {bs : List (BitVec 8)} {m : BitVec width → BitVec 8}
    {d : BitVec width → Prop} (h : bytesInMemoryHOL a bs m d) :
    ∀ j, j < bs.length → m (a + BitVec.ofNat width j) = bs.getD j 0 := by
  revert h
  induction bs generalizing a with
  | nil => intro _ j hj; simp at hj
  | cons x xs ih =>
      intro h j hj
      obtain ⟨hx, hd, ht⟩ := h
      cases j with
      | zero => simpa using hx
      | succ j =>
          have hj' : j < xs.length := by simpa using hj
          have hrec := ih ht j hj'
          rw [← addOneOffset]
          simpa using hrec

/-- The `j`-th byte of a byte list in memory lies in the domain, for every `j`
below the length.  Shared by the asmProps coverage proof and the closed
machine models (X64 and ARM8); Flapjack infrastructure, no HOL original. -/
theorem byteOffsetInDomain {width : Nat} [NeZero width]
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
          address + BitVec.ofNat width (offset + 1) := addOneOffset address offset
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
