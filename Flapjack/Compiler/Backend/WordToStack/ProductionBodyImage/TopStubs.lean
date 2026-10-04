import Flapjack.Compiler.Backend.WordToStack.ProductionBodyImage.Instructions
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile

/-! Production codec infrastructure for the two complete native top-level
stubs. No HOL declaration states these codec facts, so they carry no HOL tag.
The original native definitions, instrumentation and word payloads are retained.
These results do not assume successful decoding or a target execution. -/

namespace Flapjack.ProductionBodyImage
open Compiler.Backend Compiler.Backend.StackLang
open Compiler.Backend.WordToStack.Native Compiler.Encoders.Asm

/-- The complete handler-unwind stub has an actual production image, including
both instrumentation branches and all stack/register fields. -/
theorem raiseStubImage {width : Nat} [NeZero width] (perf : Bool) (registerCount : Nat) :
    OutputImage (raiseStubNative (width := width) perf registerCount) := by
  cases perf <;>
    simp [OutputImage, raiseStubNative, listSeq, holProgToProduction,
      holProgToProgW, Prog.map, progToProduction, storeToProduction,
      HolInst.toWordLangInst, HolArith.toWordLangArith, HolRegImm.toWordRegImm,
      wordLangInstFromHOL, wordLangArithFromHOL]

/-- The complete constant-store-and-return stub has a concrete production image. -/
theorem storeConstsStubImage {width : Nat} [NeZero width] (registerCount : Nat) :
    OutputImage (storeConstsStubNative (width := width) registerCount) := by
  simp [OutputImage, storeConstsStubNative, holProgToProduction,
    holProgToProgW, Prog.map, progToProduction]

/-- Both actual prepended stub bodies decode and invert completely. This is
derived from their native output, with no successful-output premise. -/
theorem topStubRoundtrips {width : Nat} [NeZero width] (perf : Bool) (registerCount : Nat) :
    (∃ body, holProgToProduction (raiseStubNative (width := width) perf registerCount) =
      some body ∧ productionToHolProg body =
        some (raiseStubNative (width := width) perf registerCount)) ∧
    (∃ body, holProgToProduction (storeConstsStubNative (width := width) registerCount) =
      some body ∧ productionToHolProg body =
        some (storeConstsStubNative (width := width) registerCount)) := by
  obtain ⟨raiseBody, raiseDecoded⟩ := raiseStubImage (width := width) perf registerCount
  obtain ⟨storeBody, storeDecoded⟩ := storeConstsStubImage (width := width) registerCount
  exact ⟨⟨raiseBody, raiseDecoded,
    productionToHolProg_of_holProgToProduction _ _ raiseDecoded⟩,
    ⟨storeBody, storeDecoded,
      productionToHolProg_of_holProgToProduction _ _ storeDecoded⟩⟩

end Flapjack.ProductionBodyImage
