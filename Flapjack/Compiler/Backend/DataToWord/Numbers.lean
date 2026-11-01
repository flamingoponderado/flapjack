import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Misc.Alignment

/-! Source-shaped numeric and pointer encodings for data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord
open Flapjack

/-- The source's word slice of ones between the two bit positions. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "all_ones_def"
  (words_as_type_indexed_bitvec)]
def allOnes {width : Nat} [NeZero width] (high low : Nat) : BitVec width :=
  if high ≤ low then 0 else holWordSlice (high - 1) low (~~~(0 : BitVec width))

/-- Encode a bounded field, saturating it to ones on overflow. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "maxout_bits_def"
  (words_as_type_indexed_bitvec)]
def maxoutBits {width : Nat} [NeZero width] (n bits shift : Nat) : BitVec width :=
  if n < 2 ^ bits - 1 then BitVec.ofNat width n <<< shift else allOnes (shift + bits) shift

/-- The pointer annotation's tag and length fields. This source-shaped
definition is not yet connected to the production compiler's inlined formula. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "ptr_bits_def"
  (words_as_type_indexed_bitvec)]
def ptrBits {width : Nat} [NeZero width] (conf : Config) (tag len : Nat) : BitVec width :=
  maxoutBits tag conf.tagBits (1 + conf.lenBits) ||| maxoutBits len conf.lenBits 1

/-- The signed interval represented by an immediate integer. The production
constant compiler currently expands this bound inline. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "small_int_def"
  (word_dimension_as_width := width)]
def smallInt (width : Nat) [NeZero width] (i : Int) : Prop :=
  -(Int.ofNat (2 ^ width / 8)) ≤ i ∧ i < Int.ofNat (2 ^ width / 8)

/-- Encode a signed immediate integer in the source word representation. The
production constant compiler currently expands this formula inline. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Smallnum_def"
  (words_as_type_indexed_bitvec)]
def smallnum {width : Nat} [NeZero width] (i : Int) : BitVec width :=
  if i < 0 then 0 - BitVec.ofNat width (4 * (0 - i)).toNat
  else BitVec.ofNat width (4 * i).toNat

end Flapjack.Compiler.Backend.DataToWord
