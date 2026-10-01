import Flapjack.Compiler.Backend.WordToStack.ProductionFrame
import Flapjack.Compiler.Backend.WordToStackRegFormat

namespace Flapjack
open RiscV RiscV.CakeRegAlloc
open Compiler.Backend.WordToStack.Native Compiler.Encoders.Asm

/-! Flapjack infrastructure for the concrete executed source caller. These
are not HOL simulation theorems. The native SOME formatting clause and frame
formula are compared; NONE scheduler temporaries and body/bitmaps remain open. -/

/-- The complete original executed caller record, with every field preserved. -/
theorem sourceWordStackConfig_original (label : Nat) (allocation : WordSpillState)
    (slots : Nat) : sourceWordStackConfig label allocation slots =
      { locations := allocation.locations
        scratch := cakeRiscVRegisterCount
        stackBase := 0
        addressScratch := 23
        specialScratch := cakeSpecialScratch
        carryScratch := cakeCarryScratch
        abiBase := 1
        abiStride := 1
        callAbiBase := 0
        abiRegisterCount := cakeRiscVRegisterCount
        abiFrameSlots := slots
        frameOffset := if slots = 0 then 0 else slots + 1
        sectionId := label
        handlerLabel := label } := rfl

/-- Actual call frame, including the empty case; no successful lowering premise. -/
theorem sourceWordStackConfig_callFrame (label : Nat) (allocation : WordSpillState)
    (slots : Nat) :
    wordStackCallFrameOffset (sourceWordStackConfig label allocation slots) =
      if slots = 0 then 0 else slots + 1 := by
  by_cases empty : slots = 0
  · simp [wordStackCallFrameOffset, sourceWordStackConfig, empty]
  · simp [wordStackCallFrameOffset, wordStackCakeFrameSize, sourceWordStackConfig, empty]

/-- Actual call ABI base zero matches native SOME formatting for every index,
including natural subtraction beyond the frame. Return ABI base one is separate. -/
theorem sourceWordStackConfig_callLocation (label : Nat) (allocation : WordSpillState)
    (slots index : Nat) :
    wordStackPhysicalLocation (sourceWordStackConfig label allocation slots) index
      (sourceWordStackConfig label allocation slots).callAbiBase =
      match Compiler.Backend.WordToStackRegFormat.formatVar cakeRiscVRegisterCount
          (some index) with
      | .inl register => .register register
      | .inr slot => .stack ((if slots = 0 then 0 else slots + 1) - 1 -
          (slot - cakeRiscVRegisterCount)) := by
  by_cases below : index < cakeRiscVRegisterCount
  · simp [wordStackPhysicalLocation, sourceWordStackConfig,
      Compiler.Backend.WordToStackRegFormat.formatVar, below]
  · simp [wordStackPhysicalLocation, wordStackCakeFrameSize, sourceWordStackConfig,
      Compiler.Backend.WordToStackRegFormat.formatVar, below]
    rfl

/-- Actual retained caller native frame relation. Codec failure remains NONE;
no conversion success, callback or body/bitmap relation is assumed. -/
theorem retainedAllocator_sourceConfigFrame {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (allocated : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output)
    (conf : AsmConfigExact width) (perf : Bool)
    (bitmaps : AppList (BitVec width) × Nat) :
    (wordLangProgToHOL output.colouredProgram).map
      (fun native => (compileProgNative conf perf native parameters.length
        cakeRiscVRegisterCount bitmaps).2.1) =
    (wordLangProgToHOL output.colouredProgram).map
      (fun _ => wordStackCallFrameOffset (sourceWordStackConfig label output.allocation
        (cakeWordFrameSlots output.allocation parameters output.program))) := by
  simp only [sourceWordStackConfig_callFrame]
  exact retainedAllocator_nativeCallerFrame label parameters program output allocated conf perf bitmaps

end Flapjack
