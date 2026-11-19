module

public import Flapjack.Misc.Multiword

@[expose] public section

/-! Single-word machine primitives from the HOL multiword machine-code
examples (`HOL/examples/machine-code/multiword/mc_multiwordScript.sml`). -/
namespace Flapjack.Misc.Multiword

/-- The source's non-overflow precondition for a single-word division. The
dividend operands carry independent word dimensions in the original. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "single_div_pre_def"
  (words_as_type_indexed_bitvec)]
def singleDivPre {w2 : Nat} {w0 : Nat} {w9 : Nat} [NeZero w2] [NeZero w0] [NeZero w9]
    (r2 : BitVec w2) (r0 : BitVec w0) (r9 : BitVec w9) : Prop :=
  r9 ≠ 0 ∧ (r2.toNat * 2 ^ w9 + r0.toNat) / r9.toNat < 2 ^ w9

/-- Single-word addition with a carry word, reporting the carry as a word. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "single_add_word_def"
  (words_as_type_indexed_bitvec)]
def singleAddWord {width : Nat} [NeZero width] (w1 w2 c : BitVec width) :
    BitVec width × BitVec width :=
  let (z, carry) := singleAdd w1 w2 (decide (c ≠ 0))
  (z, b2w carry)

/-- Single-word subtraction with a borrow word, reporting the borrow as a word. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "single_sub_word_def"
  (words_as_type_indexed_bitvec)]
def singleSubWord {width : Nat} [NeZero width] (w1 w2 c : BitVec width) :
    BitVec width × BitVec width :=
  let (z, carry) := singleSub w1 w2 (decide (c ≠ 0))
  (z, b2w carry)

end Flapjack.Misc.Multiword
