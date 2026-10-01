import Flapjack.Compiler.Backend.WordToStack.NativeInstructions

/-! Literal performance instrumentation syntax. This does not verify the x64 instrumentation. -/
namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Literal native performance frame setup syntax. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "perf_call_prefix_def"
  (words_as_type_indexed_bitvec)]
def perfCallPrefixNative {width : Nat} [NeZero width]
    (l1 l2 k : Nat) : HolProg width :=
  Flapjack.Compiler.Backend.StackLang.listSeq
    [ .locValue k l1 l2,
      .inst (.mem .store k
        (.addr (Flapjack.Compiler.Backend.WordToStack.perfRsp)
          (-8 : BitVec width))),
      .inst (.mem .store (Flapjack.Compiler.Backend.WordToStack.perfRbp)
        (.addr (Flapjack.Compiler.Backend.WordToStack.perfRsp)
          (-16 : BitVec width))),
      .inst (.arith (.binop .sub (Flapjack.Compiler.Backend.WordToStack.perfRsp)
        (Flapjack.Compiler.Backend.WordToStack.perfRsp) (.imm (16 : BitVec width)))),
      .inst (.arith (.binop .or (Flapjack.Compiler.Backend.WordToStack.perfRbp)
        (Flapjack.Compiler.Backend.WordToStack.perfRsp)
        (.reg (Flapjack.Compiler.Backend.WordToStack.perfRsp)))) ]

/-- Literal native performance frame teardown syntax. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "perf_call_suffix_def"
  (words_as_type_indexed_bitvec)]
def perfCallSuffixNative {width : Nat} [NeZero width] : HolProg width :=
  Flapjack.Compiler.Backend.StackLang.listSeq
    [ .inst (.mem .load (Flapjack.Compiler.Backend.WordToStack.perfRbp)
        (.addr (Flapjack.Compiler.Backend.WordToStack.perfRsp) (0 : BitVec width))),
      .inst (.arith (.binop .add (Flapjack.Compiler.Backend.WordToStack.perfRsp)
        (Flapjack.Compiler.Backend.WordToStack.perfRsp) (.imm (16 : BitVec width)))) ]


/-- Flapjack-only representation transport, without evaluation premises. -/
theorem toGeneric_perfCallPrefixNative {width : Nat} [NeZero width] (l1 l2 k : Nat) :
    toGeneric (perfCallPrefixNative (width := width) l1 l2 k) =
      WordToStackRegFormat.perfCallPrefixW l1 l2 k := by
  simp [perfCallPrefixNative, WordToStackRegFormat.perfCallPrefixW, toGeneric,
    Prog.map, listSeq, HolInst.toWordLangInst, HolArith.toWordLangArith,
    HolRegImm.toWordRegImm, HolAddr.toWordLangAddr]

/-- Flapjack-only representation transport; no instrumentation verification claim. -/
theorem toGeneric_perfCallSuffixNative {width : Nat} [NeZero width] :
    toGeneric (perfCallSuffixNative (width := width)) =
      WordToStackRegFormat.perfCallSuffixW := by
  simp [perfCallSuffixNative, WordToStackRegFormat.perfCallSuffixW, toGeneric,
    Prog.map, listSeq, HolInst.toWordLangInst, HolArith.toWordLangArith,
    HolRegImm.toWordRegImm, HolAddr.toWordLangAddr]

end Flapjack.Compiler.Backend.WordToStack.Native
