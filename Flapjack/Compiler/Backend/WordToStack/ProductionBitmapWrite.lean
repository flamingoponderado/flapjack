import Flapjack.Compiler.Backend.StackToLab.Production
import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapTransport
import Flapjack.Compiler.Backend.WordToStack.NativeLive

/-! Flapjack-specific bitmap write boundary regressions. These do not carry a
HOL tag: they expose the production macro rejection absent from native wLive,
and establish the repaired actual write boundary without an extra count guard.
This is production carrier infrastructure, not a pass-simulation theorem. -/
namespace Flapjack.ProductionBitmapWrite
open Compiler.Backend.StackLang

/-- The reviewed production macro projection rejects a bitmap index outside
its word carrier, even though the original writer wraps that index. -/
theorem macroIndexRejected {width : Nat} (register index : Nat)
    (outside : 2 ^ width ≤ index + 1) :
    ProductionMacros.projectMacros (width := width)
      (.seq (.const register (index + 1)) (.stackStore register 0)) = none := by
  simp [ProductionMacros.projectMacros, Nat.not_lt.mpr outside]

/-- A minimal positive-width boundary counterexample; no count/data-length
invariant would avoid it for all positive widths. -/
theorem widthOneIndexRejected :
    Compiler.Backend.StackToLab.Production.toNative? (width := 1)
      (.seq (.const 22 2) (.stackStore 22 0)) = none := by
  simp [Compiler.Backend.StackToLab.Production.toNative?, byteNames,
    natToWord, mapWordPayloads, ProductionMacros.projectMacros]

/-- The actual writer now passes through the shared literal instruction codec,
including indices outside the word width. Empty frames retain Skip and state. -/
theorem writerCodec {width : Nat} [NeZero width]
    (config : RiscV.WordStackConfig) (register slots : Nat)
    (state : RiscV.WordStackBitmapState) (live : List Nat)
    (builder : List Nat → List Nat) :
    natToHolProg (width := width)
      (RiscV.wordStackBitmapWriteWithBuilder config register slots state live builder).1 =
      some (if slots = 0 then .skip else
        .seq (.inst (.const register (BitVec.ofNat width (state.length + 1))))
          (.stackStore register (RiscV.wordStackOffset config 0))) := by
  by_cases empty : slots = 0 <;>
    simp [RiscV.wordStackBitmapWriteWithBuilder, empty,
      RiscV.wordStackInsertBitmap, natToHolProg, byteNames, natToWord,
      mapWordPayloads, mapInstPayloads, productionToHolProg, progFromProduction,
      Flapjack.wordLangInstToHOL, Compiler.Backend.progWToHolProg,
      Prog.map, Compiler.Encoders.Asm.HolInst.ofWordLangInst]

/-- The actual Stack-to-Lab consumer accepts this repaired prefix for every
stored count; it does not rely on the bounded macro projection. -/
theorem writerConsumer {width : Nat} [NeZero width]
    (config : RiscV.WordStackConfig) (register slots : Nat)
    (state : RiscV.WordStackBitmapState) (live : List Nat)
    (builder : List Nat → List Nat) :
    Compiler.Backend.StackToLab.Production.toNative? (width := width)
      (RiscV.wordStackBitmapWriteWithBuilder config register slots state live builder).1 =
      some (if slots = 0 then .skip else
        .seq (.inst (.const register (BitVec.ofNat width (state.length + 1))))
          (.stackStore register (RiscV.wordStackOffset config 0))) := by
  by_cases empty : slots = 0 <;>
    simp [RiscV.wordStackBitmapWriteWithBuilder, empty,
      RiscV.wordStackInsertBitmap, Compiler.Backend.StackToLab.Production.toNative?,
      byteNames, natToWord, mapWordPayloads, mapInstPayloads,
      ProductionMacros.projectMacros, productionToHolProg, progFromProduction,
      wordLangInstToHOL, Compiler.Backend.progWToHolProg,
      Prog.map, Compiler.Encoders.Asm.HolInst.ofWordLangInst]

/-- The executed post-flattening converter puts the index in the same word
carrier used by the canonical writer. Neither register nor index is bounded. -/
theorem indexEmission {width : Nat} [NeZero width] (register index : Nat) :
    RiscV.labCompilePlain (width := width)
      (RiscV.labPlainNatToWord (.word (.const register (index + 1)))) =
    RiscV.labCompilePlain
      (.word (.const register (BitVec.ofNat width (index + 1)))) := by
  rfl

/-- Actual encoded line sizing sees the wrapped value as well; this matters
when wrapping changes the constant instruction sequence length. -/
theorem indexLength {width : Nat} [NeZero width] (register index : Nat) :
    RiscV.labLineInstructionCount (width := width)
      (.asm (RiscV.labPlainNatToWord (.word (.const register (index + 1)))) [] 0) =
    RiscV.labLineInstructionCount
      (.asm (.word (.const register (BitVec.ofNat width (index + 1)))) [] 0) := by
  rfl

end Flapjack.ProductionBitmapWrite
