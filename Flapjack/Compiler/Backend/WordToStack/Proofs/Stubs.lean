import Flapjack.Compiler.Backend.WordToStack.NativeStubs

namespace Flapjack.WordToStackProofs
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Full original non-instrumented handler-unwind sequence. The original
arbitrary register and all eight commands are retained; this is a program
syntax equality and does not assume or assert a target execution. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "raise_stub_F"
  (words_as_type_indexed_bitvec)]
theorem raiseStubFalse {width : Nat} [NeZero width] (k : Nat) :
    raiseStubNative (width := width) false k =
      (.seq (.get k .handler)
        (.seq (.stackSetSize k)
          (.seq .skip
            (.seq (.stackLoad k 2)
              (.seq (.set .handler k)
                (.seq (.stackLoad k 1)
                  (.seq (.stackFree 3) (.raise k))))))) :
        Flapjack.Compiler.Backend.StackLang.Prog (HolInst width) HolCmp (HolRegImm width) HolBinop HolMemop
          (HolAddr width) Flapjack.Basis.Pure.MlString.MlString) := by
  rfl

end Flapjack.WordToStackProofs
