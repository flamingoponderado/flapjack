import Flapjack.HolRef
import Init.Data.BitVec.Bitblast
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack

/-- Full original even-register maximum. GENLIST is the natural range mapped
by its index function; MAX_LIST is natural maximum with empty default zero,
expressed by the associative maximum fold. No external source tag is added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAX_LIST_GENLIST_evens"]
theorem maxListGenlistEvens (n : Nat) :
    ((List.range n).map (fun x => 2 * x)).foldl max 0 = 2 * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rw [Nat.max_eq_right (by omega)]
    omega

/-- Full original one-based even-register maximum, including the empty list. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAX_LIST_GENLIST_evens2"]
theorem maxListGenlistEvens2 (n : Nat) :
    ((List.range n).map (fun x => 2 * (x + 1))).foldl max 0 = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rw [Nat.max_eq_right (by omega)]

/-- Full original local zero-OR characterisation at every positive dimension. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_or_eq_0"
  (words_as_type_indexed_bitvec)]
theorem wordOrEqZero {width : Nat} [NeZero width] (w v : BitVec width) :
    w ||| v = 0 ↔ w = 0 ∧ v = 0 := BitVec.or_eq_zero_iff

/-- Full original shift reversal under exactly the original non-MSB guard. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "shift_shift_lemma"
  (words_as_type_indexed_bitvec)]
theorem shiftShiftLemma {width : Nat} [NeZero width] (w : BitVec width)
    (h : w.msb = false) : (w <<< 1) >>> 1 = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hnext : 1 + i < width
  · simp [hnext, BitVec.getLsbD_eq_getElem hi]
  · have last : i = width - 1 := by omega
    have hb : w.getLsbD i = false := by
      simpa [BitVec.msb_eq_getLsbD_last, ← last] using h
    simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hnext, hb]

/-- Full original bitmap low-bit insertion identity; no no-overflow or MSB
premise is required, including at the one-bit word dimension. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_shift_or_1"
  (words_as_type_indexed_bitvec)]
theorem wordShiftOrOne {width : Nat} [NeZero width] (n : BitVec width) :
    (n <<< 1) ||| 1 = (n <<< 1) + 1 := by
  symm
  apply BitVec.add_eq_or_of_and_eq_zero
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hzero : i = 0
  · subst i; simp
  · simp [BitVec.getLsbD_one, hzero]

end Flapjack.Compiler.Backend.WordToStack
