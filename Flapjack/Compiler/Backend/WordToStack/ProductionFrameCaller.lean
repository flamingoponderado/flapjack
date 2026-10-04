import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapCaller
import Flapjack.Compiler.Backend.WordToStack.ProductionFrame
import Flapjack.Compiler.Backend.WordToStack.ProductionLocations
import Flapjack.Compiler.Backend.WordToStack.ProductionConfiguration

/-! Actual native-copy caller frame correspondence. These compiler carrier
facts have no standalone HOL declarations; they do not assert body simulation. -/
namespace Flapjack.ProductionFrameCaller
open RiscV RiscV.CakeRegAlloc ProductionGcCutsets ProductionCleanupConventions
open Compiler.Backend.WordToStack.Native Compiler.Encoders.Asm

/-- The real retained allocation and its derived native input supply an actual
encoding of the coloured body and the complete native frame equation. No codec
success, maximum equality or desired frame relation is assumed. Generic stage
functions permit instantiation at the executed native-copy pipeline. -/
theorem retainedNativeFrame {width : Nat} [NeZero width]
    (copy dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some output)
    (input : NativeInput output.program)
    (config : AsmConfigExact width) (perf : Bool)
    (bitmaps : AppList (BitVec width) × Nat) (renamedProgram : WordProg (BitVec width)) :
    ∃ native, wordLangProgToHOL output.colouredProgram = some native ∧
      (compileProgNative config perf native parameters.length cakeRiscVRegisterCount bitmaps).2.1 =
        let slots := cakeWordFrameSlots output.allocation parameters renamedProgram
        if slots = 0 then 0 else slots + 1 := by
  obtain ⟨before, encoded, _, _⟩ := input.encoded output.program
  have accepted : (wordLangProgToHOL output.colouredProgram).isSome = true := by
    rw [CakeAllocationWithColour.colouredProgram, wordLangProgToHOL_wordApplyColour_isSome]
    simp only [encoded, Option.isSome_some]
  obtain ⟨native, encoding⟩ := Option.isSome_iff_exists.mp accepted
  refine ⟨native, encoding, ?_⟩
  have maximum := wordProgCakeMaxVar_codec output.colouredProgram
  simp only [encoding, Option.map_some, Option.some.injEq] at maximum
  rw [ProductionBitmapCaller.retainedConsumer_frameSlots copy dead unreach ssa
    label parameters source output produced renamedProgram]
  simp only [compileProgNative, cakeColourFrameSlots]
  rw [maximum]
  rfl

/-- Every operand lookup in the real retained allocator uses native formatting
at the native compiler's actual frame. Absence remains explicit; duplicate names,
odd colours and natural subtraction outside the frame are preserved. This is
Flapjack carrier infrastructure, not a semantic HOL theorem. -/
theorem retainedNativeLocations {width : Nat} [NeZero width]
    (copy dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some output)
    (input : NativeInput output.program)
    (config : AsmConfigExact width) (perf : Bool)
    (bitmaps : AppList (BitVec width) × Nat) (renamedProgram : WordProg (BitVec width)) :
    ∃ native, wordLangProgToHOL output.colouredProgram = some native ∧
      (∀ name, lookupNatInfo name output.allocation.locations =
        if name ∈ parameters ++ wordProgVariables output.program then
          some (match Compiler.Backend.WordToStackRegFormat.formatVar cakeRiscVRegisterCount
              (some (CakeAlloc.totalColour output.colouring name / 2)) with
            | .inl register => .register register
            | .inr slot => .stack ((compileProgNative config perf native parameters.length
                cakeRiscVRegisterCount bitmaps).2.1 - 1 - (slot - cakeRiscVRegisterCount)))
        else none) ∧
      wordStackCallFrameOffset (sourceWordStackConfig label output.allocation
        (cakeWordFrameSlots output.allocation parameters renamedProgram)) =
        (compileProgNative config perf native parameters.length cakeRiscVRegisterCount bitmaps).2.1 := by
  obtain ⟨native, encoding, frame⟩ := retainedNativeFrame copy dead unreach ssa
    label parameters source output produced input config perf bitmaps renamedProgram
  obtain ⟨spill, _⟩ := allocatorWithCopy_retained copy dead unreach ssa
    label parameters source output produced
  have physicalFrame :
      (cakeColourFrameSlots cakeRiscVRegisterCount parameters output.program output.colouring).2 =
      (compileProgNative config perf native parameters.length cakeRiscVRegisterCount bitmaps).2.1 := by
    rw [frame, ProductionBitmapCaller.retainedConsumer_frameSlots copy dead unreach ssa
      label parameters source output produced renamedProgram]
    rfl
  refine ⟨native, encoding, ?_, ?_⟩
  · intro name
    rw [spill, cakeColourWordSpillState_lookup, cakeColourLocation_formatVar, physicalFrame]
    rfl
  · rw [sourceWordStackConfig_callFrame, frame]

/-- At the executed source-row boundary, the actual PanToWord producer supplies
native-input conventions and codec success. The observed native-copy allocation
supplies the actual colouring, spill locations and caller frame. No output codec,
source-image callback, target evaluation or desired frame equation is assumed. -/
theorem panToWordRowNativeFrame {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions)
    (config : AsmConfigExact width) (perf : Bool)
    (bitmaps : AppList (BitVec width) × Nat)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label
      (wordSsaAbiParameters arity) (wordBeforeSsaAllocatorBody body) = some output)
    (renamedProgram : WordProg (BitVec width)) :
    ∃ (retained : CakeAllocationWithColour (BitVec width))
      (native : WordLangProgHOL (BitVec width)),
      retained.toLegacy = output ∧
      wordLangProgToHOL retained.colouredProgram = some native ∧
      (compileProgNative config perf native arity cakeRiscVRegisterCount bitmaps).2.1 =
        let slots := cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram
        if slots = 0 then 0 else slots + 1 := by
  have input := panToWordRow_input functions label arity body row config output produced
  have accepted := panToWordRow_codec functions label arity body row
  obtain ⟨before, encoded⟩ := Option.isSome_iff_exists.mp
    (wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body accepted)
  unfold cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy at produced
  simp only [encoded] at produced
  obtain ⟨retained, actualRun, same⟩ := Option.map_eq_some_iff.mp produced
  subst output
  obtain ⟨native, encoding, frame⟩ := retainedNativeFrame _ _ _ _ label
    (wordSsaAbiParameters arity) _ retained actualRun input config perf bitmaps renamedProgram
  refine ⟨retained, native, rfl, encoding, ?_⟩
  have count : (wordSsaAbiParameters arity).length = arity := by
    simp only [wordSsaAbiParameters, List.length_map, List.length_range]
  rw [count] at frame
  exact frame

/-- Complete operand and call-area configuration at the executed source-row
boundary. The source producer discharges the native-input/codec obligations;
the actual native-copy allocation supplies colouring, name domain and frame.
All operand names and call indices are covered, including absent names and
natural subtraction outside the frame. No desired output relation is assumed. -/
theorem panToWordRowNativeLocations {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions)
    (config : AsmConfigExact width) (perf : Bool)
    (bitmaps : AppList (BitVec width) × Nat)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label
      (wordSsaAbiParameters arity) (wordBeforeSsaAllocatorBody body) = some output)
    (renamedProgram : WordProg (BitVec width)) :
    ∃ (retained : CakeAllocationWithColour (BitVec width))
      (native : WordLangProgHOL (BitVec width)),
      retained.toLegacy = output ∧
      wordLangProgToHOL retained.colouredProgram = some native ∧
      (∀ name, lookupNatInfo name output.2.2.2.locations =
        if name ∈ wordSsaAbiParameters arity ++ wordProgVariables output.2.2.1 then
          some (match Compiler.Backend.WordToStackRegFormat.formatVar cakeRiscVRegisterCount
              (some (CakeAlloc.totalColour retained.colouring name / 2)) with
            | .inl register => .register register
            | .inr slot => .stack ((compileProgNative config perf native arity
                cakeRiscVRegisterCount bitmaps).2.1 - 1 - (slot - cakeRiscVRegisterCount)))
        else none) ∧
      (let caller := sourceWordStackConfig label output.2.2.2
        (cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram)
       wordStackCallFrameOffset caller =
         (compileProgNative config perf native arity cakeRiscVRegisterCount bitmaps).2.1) ∧
      (∀ index,
        let caller := sourceWordStackConfig label output.2.2.2
          (cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram)
        wordStackPhysicalLocation caller index caller.callAbiBase =
          match Compiler.Backend.WordToStackRegFormat.formatVar cakeRiscVRegisterCount
              (some index) with
          | .inl register => .register register
          | .inr slot => .stack ((compileProgNative config perf native arity
              cakeRiscVRegisterCount bitmaps).2.1 - 1 - (slot - cakeRiscVRegisterCount))) := by
  have input := panToWordRow_input functions label arity body row config output produced
  have accepted := panToWordRow_codec functions label arity body row
  obtain ⟨before, encoded⟩ := Option.isSome_iff_exists.mp
    (wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body accepted)
  unfold cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy at produced
  simp only [encoded] at produced
  obtain ⟨retained, actualRun, same⟩ := Option.map_eq_some_iff.mp produced
  subst output
  obtain ⟨native, encoding, locations, frame⟩ := retainedNativeLocations _ _ _ _ label
    (wordSsaAbiParameters arity) _ retained actualRun input config perf bitmaps renamedProgram
  have count : (wordSsaAbiParameters arity).length = arity := by
    simp only [wordSsaAbiParameters, List.length_map, List.length_range]
  rw [count] at locations frame
  refine ⟨retained, native, rfl, encoding, locations, frame, ?_⟩
  intro index
  dsimp only
  rw [sourceWordStackConfig_callFrame] at frame
  rw [sourceWordStackConfig_callLocation, ← frame]
  rfl

end Flapjack.ProductionFrameCaller
