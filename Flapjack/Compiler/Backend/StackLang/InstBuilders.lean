import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Compiler.Backend.StackLang

/-! Literal native stackLangScript.sml:68–87 combinators required by the
complete stack_remove compiler. Production routing remains open on 36ez.3.
-/
namespace Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- The original While overload is a Loop/If with Break zero. -/
@[hol "cakeml/compiler/backend/stackLangScript.sml" "While"
  (words_as_type_indexed_bitvec)]
def whileProg {width : Nat} [NeZero width] (comparison : HolCmp) (register : Nat)
    (right : HolRegImm width) (body : HolProg width) : HolProg width :=
  .loop (.ite comparison register right body (.break 0))

/-- The original move uses Or with the source in both operand positions. -/
@[hol "cakeml/compiler/backend/stackLangScript.sml" "move"
  (words_as_type_indexed_bitvec)]
def moveInst {width : Nat} [NeZero width] (destination source : Nat) : HolProg width :=
  .inst (.arith (.binop .or destination source (.reg source)))

@[hol "cakeml/compiler/backend/stackLangScript.sml" "sub_inst"
  (words_as_type_indexed_bitvec)]
def subInst {width : Nat} [NeZero width] (destination source : Nat) : HolProg width :=
  .inst (.arith (.binop .sub destination destination (.reg source)))

@[hol "cakeml/compiler/backend/stackLangScript.sml" "add_inst"
  (words_as_type_indexed_bitvec)]
def addInst {width : Nat} [NeZero width] (destination source : Nat) : HolProg width :=
  .inst (.arith (.binop .add destination destination (.reg source)))

/-- bytes_in_word is n2w(dimindex DIV8), including dimensions below eight. -/
@[hol "cakeml/compiler/backend/stackLangScript.sml" "add_bytes_in_word_inst"
  (words_as_type_indexed_bitvec)]
def addBytesInWordInst {width : Nat} [NeZero width] (register : Nat) : HolProg width :=
  .inst (.arith (.binop .add register register (.imm (BitVec.ofNat width (width / 8)))))

/-- Native single-word specialization of the literal list_Seq recursion. -/
@[hol "cakeml/compiler/backend/stackLangScript.sml" "list_Seq_def"
  (words_as_type_indexed_bitvec)]
def listSeqHOL {width : Nat} [NeZero width] (programs : List (HolProg width)) : HolProg width :=
  listSeq programs

end Flapjack.Compiler.Backend.StackLang
