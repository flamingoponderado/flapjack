import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers

namespace Flapjack.WordToStackProofs
open Flapjack

/-- Flapjack infrastructure: one native byte-stride step followed by a list
length displacement is the successor-length displacement, in the modular word
carrier. No arithmetic bound or nonzero-stride premise is needed. -/
private theorem addressStep {width : Nat} [NeZero width] (a : BitVec width) (n : Nat) :
    (a + wordSemBytesInWord) + wordSemBytesInWord * BitVec.ofNat width n =
      a + wordSemBytesInWord * BitVec.ofNat width (n+1) := by
  simp only [BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one]
  rw [BitVec.add_assoc, BitVec.add_comm wordSemBytesInWord]

/-- Full original native constant-write append law. The conclusion is equality
of whole memory functions, for arbitrary memory, flags, values, base and offset.
Every word-width/address/relocation overflow and zero byte stride is retained. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "const_writes_append"
  (words_as_type_indexed_bitvec)]
theorem constWritesAppend {width : Nat} [NeZero width]
    (h t : List (Bool × BitVec width)) (a off : BitVec width)
    (m : BitVec width → WordLocW width) :
    wordSemConstWrites a off (h ++ t) m =
      wordSemConstWrites (a + wordSemBytesInWord * BitVec.ofNat width h.length) off t
        (wordSemConstWrites a off h m) := by
  induction h generalizing a m with
  | nil => simp [wordSemConstWrites]
  | cons entry h ih =>
    rcases entry with ⟨b,x⟩
    simp only [List.cons_append, wordSemConstWrites, ih, List.length_cons]
    rw [addressStep]

/-- Full original native constant-address append law. Both full domain
predicates are checked at exactly the original modularly advanced addresses;
there is no disjointness, address-range, or stride-width assumption. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "const_addresses_append"
  (words_as_type_indexed_bitvec)]
theorem constAddressesAppend {width : Nat} [NeZero width]
    (xs ys : List (Bool × BitVec width)) (dm : BitVec width → Bool) (a : BitVec width) :
    wordSemConstAddresses a (xs ++ ys) dm = true ↔
      wordSemConstAddresses a xs dm = true ∧
      wordSemConstAddresses (a + wordSemBytesInWord * BitVec.ofNat width xs.length) ys dm = true := by
  induction xs generalizing a with
  | nil => simp [wordSemConstAddresses]
  | cons entry xs ih =>
    simp only [List.cons_append, wordSemConstAddresses, Bool.and_eq_true, ih,
      List.length_cons]
    rw [addressStep]
    exact and_assoc.symm

end Flapjack.WordToStackProofs
