import Flapjack.Compiler.Backend.WordCse.RegisterUses

/-! Full original encoding injectivity prerequisites. No register, word range
or well-formedness guard is added. Arithmetic simulation remains separate. -/
namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm

@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wordToNum_unique"
  (words_as_type_indexed_bitvec)]
theorem wordToNumUnique {width : Nat} [NeZero width] (c1 c2 : BitVec width) :
    wordToNum c1 = wordToNum c2 ↔ c1 = c2 := by
  exact BitVec.toNat_inj

@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "arithOpToNum_eq"]
theorem arithOpToNumEq (op1 op2 : BinOp) :
    arithOpToNum op1 = arithOpToNum op2 ↔ op1 = op2 := by
  cases op1 <;> cases op2 <;> simp [arithOpToNum]

@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "memOpToNum_eq"]
theorem memOpToNumEq (op1 op2 : HolMemop) :
    memOpToNum op1 = memOpToNum op2 ↔ op1 = op2 := by
  cases op1 <;> cases op2 <;> simp [memOpToNum]

@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "shiftToNum_eq"]
theorem shiftToNumEq (s1 s2 : Shift) :
    shiftToNum s1 = shiftToNum s2 ↔ s1 = s2 := by
  cases s1 <;> cases s2 <;> simp [shiftToNum]

end Flapjack.Compiler.Backend.WordCse
