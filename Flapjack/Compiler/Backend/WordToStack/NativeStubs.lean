import Flapjack.Compiler.Backend.WordToStack.NativeInstructions

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Literal native handler-unwind stub; instrumentation syntax only. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "raise_stub_def" (words_as_type_indexed_bitvec)]
def raiseStubNative {width : Nat} [NeZero width] (perf : Bool) (k : Nat) : HolProg width :=
  .seq (.get k .handler)
    (.seq (.stackSetSize k)
      (.seq
        (if perf then
          Flapjack.Compiler.Backend.StackLang.listSeq
            [ .stackLoad k 3,
              .inst (.arith (.binop .or (Flapjack.Compiler.Backend.WordToStack.perfRsp)
                k (.reg k))),
              .stackLoad k 4,
              .inst (.arith (.binop .or (Flapjack.Compiler.Backend.WordToStack.perfRbp)
                k (.reg k))) ]
        else .skip)
        (.seq (.stackLoad k 2)
          (.seq (.set .handler k)
            (.seq (.stackLoad k 1)
              (.seq (.stackFree (Flapjack.Compiler.Backend.WordToStack.handlerSlots perf))
                (.raise k)))))))

/-- Literal native constant-pool store-and-return stub. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "store_consts_stub_def" (words_as_type_indexed_bitvec)]
def storeConstsStubNative {width : Nat} [NeZero width] (k : Nat) : HolProg width :=
  .seq (.storeConsts k (k + 1) none) (.ret 0)


/-- Flapjack-only universal representation transport, no evaluation premise. -/
theorem toGeneric_raiseStubNative {width : Nat} [NeZero width] (perf : Bool) (k : Nat) :
    toGeneric (raiseStubNative (width := width) perf k) =
      WordToStackRegFormat.raiseStub perf k := by
  cases perf <;> simp [raiseStubNative, WordToStackRegFormat.raiseStub, toGeneric,
    Prog.map, listSeq, HolInst.toWordLangInst, HolArith.toWordLangArith,
    HolRegImm.toWordRegImm]

/-- Flapjack-only universal representation transport, no HOL original. -/
theorem toGeneric_storeConstsStubNative {width : Nat} [NeZero width] (k : Nat) :
    toGeneric (storeConstsStubNative (width := width) k) =
      WordToStackRegFormat.storeConstsStub k := by
  simp [storeConstsStubNative, WordToStackRegFormat.storeConstsStub, toGeneric, Prog.map]

end Flapjack.Compiler.Backend.WordToStack.Native
