import Flapjack.HolRef
import Flapjack.Pancake.WordLang

/-! Primitive word operations of the faithful assembly semantics.
Counterpart of `cakeml/compiler/encoders/asm/asmSemScript.sml`.
-/

namespace Flapjack.Compiler.Encoders.AsmSem

/-- HOL's total word shift. The LabSem arithmetic transition applies its
separate range assertion after updating the destination with this result;
the operation itself neither rejects nor masks the shift amount. -/
@[hol "cakeml/compiler/encoders/asm/asmSemScript.sml" "word_shift_def"
  (words_as_type_indexed_bitvec)]
def wordShift {width : Nat} [NeZero width] (operator : Flapjack.Shift)
    (value : BitVec width) (amount : Nat) : BitVec width :=
  match operator with
  | .lsl => value <<< amount
  | .lsr => value >>> amount
  | .asr => BitVec.sshiftRight value amount
  | .ror => BitVec.rotateRight value amount

end Flapjack.Compiler.Encoders.AsmSem
