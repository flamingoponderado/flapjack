import Flapjack.HolRef
import Std.Tactic

namespace Flapjack.StackSem

/-- HOL's recursive word bit length, including the zero-word base case.
    Positive-width BitVec represents the HOL type-indexed word dimension. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "bit_length_def"
  (words_as_type_indexed_bitvec)]
def bitLength {width : Nat} [NeZero width] (word : BitVec width) : Nat :=
  if word = 0 then 0 else bitLength (word >>> 1) + 1
termination_by word.toNat
decreasing_by
  have hp : 0 < word.toNat := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply ‹¬word = 0›
    exact BitVec.eq_of_toNat_eq hz
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self hp (by decide)

/-- HOL bitmap decoding: continuation words contribute width minus one bits,
    terminal words contribute bit_length minus one bits, least significant first.
    This is a word/list definition; no refinement of the Nat utility or execution
    through the full StackSem evaluator is asserted here. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "read_bitmap_def"
  (words_as_type_indexed_bitvec)]
def readBitmap {width : Nat} [NeZero width] : List (BitVec width) → Option (List Bool)
  | [] => none
  | word :: words =>
      if word.msb then
        match readBitmap words with
        | none => none
        | some bits => some ((List.range (width - 1)).map word.getLsbD ++ bits)
      else some ((List.range (bitLength word - 1)).map word.getLsbD)

end Flapjack.StackSem
