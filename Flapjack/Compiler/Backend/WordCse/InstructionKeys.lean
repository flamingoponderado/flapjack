import Flapjack.Compiler.Encoders.Asm

/-! Literal instruction-key group from word_cseScript. Native instruction
carriers retain all overflow and FP cases. HOL words use positive-width
BitVecs; all other carriers are constructor-for-constructor. Ignored destination
registers follow the original clauses, except FPFma deliberately retains all
three registers. Memory instructions use the original catch-all key [1]. No knowledge-map carrier, CSE
simulation theorem, or executed compiler replacement is established here.
-/
namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm

@[hol "cakeml/compiler/backend/word_cseScript.sml" "wordToNum_def"
  (words_as_type_indexed_bitvec)]
def wordToNum {width : Nat} [NeZero width] (word : BitVec width) : Nat := word.toNat

@[hol "cakeml/compiler/backend/word_cseScript.sml" "shiftToNum_def"]
def shiftToNum : Shift → Nat
  | .lsl => 40
  | .lsr => 41
  | .asr => 42
  | .ror => 43

@[hol "cakeml/compiler/backend/word_cseScript.sml" "arithOpToNum_def"]
def arithOpToNum : BinOp → Nat
  | .add => 35
  | .sub => 36
  | .and => 37
  | .or => 38
  | .xor => 39

@[hol "cakeml/compiler/backend/word_cseScript.sml" "regImmToNumList_def"
  (words_as_type_indexed_bitvec)]
def regImmToNumList {width : Nat} [NeZero width] : HolRegImm width → List Nat
  | .reg r => [33, r + 100]
  | .imm word => [34, wordToNum word]

-- riscv-mi: declaration over the reduced integer carrier.
def arithToNumList {width : Nat} [NeZero width] : HolArith width → List Nat
  | .binop op _ r2 ri => [25, arithOpToNum op, r2 + 100] ++ regImmToNumList ri
  | .longMul _ _ r3 r4 => [26, r3 + 100, r4 + 100]
  | .longDiv _ _ r3 r4 r5 => [27, r3 + 100, r4 + 100, r5 + 100]
  | .shift op _ r2 ri => [28, shiftToNum op, r2 + 100] ++ regImmToNumList ri
  | .div _ r2 r3 => [29, r2 + 100, r3 + 100]
  | .addCarry _ r2 r3 _ => [30, r2 + 100, r3 + 100]
  | .addOverflow _ r2 r3 _ => [31, r2 + 100, r3 + 100]
  | .subOverflow _ r2 r3 _ => [32, r2 + 100, r3 + 100]

@[hol "cakeml/compiler/backend/word_cseScript.sml" "memOpToNum_def"]
def memOpToNum : HolMemop → Nat
  | .load => 21
  | .load8 => 22
  | .load16 => 46
  | .load32 => 44
  | .store => 23
  | .store8 => 47
  | .store16 => 24
  | .store32 => 45

@[hol "cakeml/compiler/backend/word_cseScript.sml" "loadToNumList_def"
  (words_as_type_indexed_bitvec)]
def loadToNumList {width : Nat} [NeZero width] (op : HolMemop) (address : Nat)
    (offset : BitVec width) : List Nat :=
  [memOpToNum op, address + 100, wordToNum offset]


-- riscv-mi: integer-only specialization of the referenced HOL declaration.

def instToNumList {width : Nat} [NeZero width] : HolInst width → List Nat
  | .const _ word => [2, wordToNum word]
  | .arith operation => 3 :: arithToNumList operation
  | _ => [1]

@[hol "cakeml/compiler/backend/word_cseScript.sml" "OpCurrHeapToNumList_def"]
def opCurrHeapToNumList (op : BinOp) (register : Nat) : List Nat :=
  [0, arithOpToNum op, register + 100]

end Flapjack.Compiler.Backend.WordCse
