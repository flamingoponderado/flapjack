import Flapjack.Misc.BytesInMem

namespace Flapjack.Compiler.Backend.LabToTarget

/-- Local word arithmetic infrastructure; no independent HOL original.
The increment and offset are word additions, including wraparound. -/
private theorem advanceAddress {width : Nat} (a : BitVec width) (n : Nat) :
    (a + 1) + BitVec.ofNat width n = a + BitVec.ofNat width (n + 1) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  exact congrArg (a + ·) (BitVec.add_comm 1 (BitVec.ofNat width n))

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "bytes_in_mem_APPEND"
  (words_as_type_indexed_bitvec)]
theorem bytesInMem_append {width : Nat} [NeZero width] {Value : Type}
    (xs ys : List Value) (a : BitVec width) (memory : BitVec width → Value)
    (domain excluded : BitVec width → Prop) :
    bytesInMemHOL a (xs ++ ys) memory domain excluded ↔
      bytesInMemHOL a xs memory domain excluded ∧
      bytesInMemHOL (a + BitVec.ofNat width xs.length) ys memory domain excluded := by
  induction xs generalizing a with
  | nil => simp [bytesInMemHOL]
  | cons value xs ih =>
    simp only [List.cons_append, bytesInMemHOL, List.length_cons, ih]
    rw [← advanceAddress]
    simp only [and_assoc]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "bytes_in_mem_UPDATE"
  (words_as_type_indexed_bitvec)]
theorem bytesInMem_update {width : Nat} [NeZero width] {Value : Type}
    (values : List Value) (a : BitVec width) (memory : BitVec width → Value)
    (domain excluded : BitVec width → Prop) (w1 : BitVec width) (w2 : Value) :
    (∀ n, n < values.length → a + BitVec.ofNat width n ≠ w1) ∧
      bytesInMemHOL a values memory domain excluded →
      bytesInMemHOL a values (fun address => if address = w1 then w2 else memory address)
        domain excluded := by
  induction values generalizing a with
  | nil => simp [bytesInMemHOL]
  | cons value values ih =>
    intro h
    have hne : a ≠ w1 := by simpa using h.1 0 (by simp)
    have hrel := h.2
    simp only [bytesInMemHOL] at hrel ⊢
    refine ⟨hrel.1, hrel.2.1, ?_, ?_⟩
    · simpa [hne] using hrel.2.2.1
    · apply ih (a + 1)
      refine ⟨?_, hrel.2.2.2⟩
      intro n hn
      rw [advanceAddress]
      exact h.1 (n + 1) (by simp only [List.length_cons]; omega)

end Flapjack.Compiler.Backend.LabToTarget
