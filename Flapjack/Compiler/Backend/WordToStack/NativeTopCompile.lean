import Flapjack.Compiler.Backend.WordToStack.NativeConfig
import Flapjack.Compiler.Backend.WordToStack.NativePrograms
import Flapjack.Compiler.Backend.WordToStack.NativeStubs

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Complete native top-level compiler, including the initial bitmap, exact
sparse frame map, extra frame entry and the two prepended stubs. Identifier
keys are natural numbers here, as constrained by the source configuration
and stub locations; the inner program-list compiler remains polymorphic. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
def compileNative {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    List (BitVec width) × Config × List Nat × List (Nat × HolProg width) :=
  let registerCount := conf.regCount - (5 + conf.avoidRegs.length)
  let initialBitmaps : AppList (BitVec width) × Nat :=
    if perf then (.list [16], 1) else (.list [4], 1)
  let (bodies, frames, bitmaps) :=
    compileWordToStackNative conf perf registerCount programs initialBitmaps
  let frameMap := sptFromAList ((bodies.zip frames).map fun ((identifier, _), frame) =>
    (identifier, frame))
  (appListAppend bitmaps.1,
    { bitmapsLength := bitmaps.2, stackFrameSize := frameMap },
    0 :: frames,
    (raiseStubLocation, raiseStubNative perf registerCount) ::
      (storeConstsStubLocation, storeConstsStubNative registerCount) :: bodies)

end Flapjack.Compiler.Backend.WordToStack.Native
