import Flapjack.Compiler.Backend.WordToStack.ProductionBodyImage.SourceDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionBodyImage.Traversal
import Flapjack.Compiler.Backend.WordToStack.ProductionBodyImage.RemoveMustTerminate
import Flapjack.Compiler.Backend.StackLang.WordPayloads

/-! Complete native source-row output through the production carrier boundary.
Flapjack-only compiler infrastructure, not a HOL semantic theorem or a claim
that the CLI uses this API. Input domains, decoder success and numeric bounds
are derived. The original removal pass and complete native result are retained;
the exact frame and threaded bitmap state are copied without reconstruction. -/

namespace Flapjack.ProductionBodyImage
open Compiler.Backend Compiler.Backend.StackLang
open Compiler.Backend.WordToStack.Native Compiler.Encoders.Asm
open RiscV RiscV.CakeRegAlloc ProductionCleanupConventions

/-- Complete native function output image, including its real stack allocation
prefix. Both source-side instruction guards are supplied by SourceDomain. -/
theorem compileProgNativeOutputImage {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (perf : Bool)
    (native : WordLangProgHOL (BitVec width)) (production : WordProg (BitVec width))
    (decoded : wordLangProgFromHOL native = some production)
    (supported : allocatorMemorySupported production = true)
    (arity registers : Nat) (bitmaps : AppList (BitVec width) × Nat) :
    OutputImage (compileProgNative config perf native arity registers bitmaps).1 := by
  dsimp only [compileProgNative]
  apply sequenceImage
  · have allocationImage (words : Nat) : OutputImage (.stackAlloc words : HolProg width) := by
      refine ⟨.stackAlloc words, ?_⟩
      simp [holProgToProduction, holProgToProgW, Prog.map, progToProduction]
    exact allocationImage _
  · exact compNativeOutputImage config perf native production decoded supported bitmaps _

/-- Callable native output boundary. The original post-allocation removal runs
before compilation; decoding failure remains explicit until the caller theorem
derives its absence. Bitmap state remains width typed, while code word payloads
alone project to Nat for the existing downstream production carrier. -/
def compileRetainedNativeRow? {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (perf : Bool) (arity : Nat)
    (bitmaps : AppList (BitVec width) × Nat)
    (retained : CakeAllocationWithColour (BitVec width)) :
    Option (StackProg Nat × Nat × (AppList (BitVec width) × Nat)) := do
  let native ← wordLangProgToHOL retained.colouredProgram
  let compiled := compileProgNative config perf (WordRemove.removeMustTerminate native)
    arity cakeRiscVRegisterCount bitmaps
  let body ← holProgToProduction compiled.1
  pure (WordPayloads.wordsToNat body, compiled.2)

/-- Actual retained allocator output derives successful complete native row
conversion and its lossless inverse. The returned frame/bitmap pair is exactly
the original compiler result, not a desired metadata relation premise. -/
theorem retainedNativeRowOutput {width : Nat} [NeZero width]
    (copy dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option
      (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (retained : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some retained)
    (input : NativeInput retained.program)
    (config : AsmConfigExact width) (perf : Bool) (arity : Nat)
    (bitmaps : AppList (BitVec width) × Nat) :
    ∃ (native : WordLangProgHOL (BitVec width)) (typed : StackProg (BitVec width)),
      wordLangProgToHOL retained.colouredProgram = some native ∧
      let compiled := compileProgNative config perf (WordRemove.removeMustTerminate native)
        arity cakeRiscVRegisterCount bitmaps
      holProgToProduction compiled.1 = some typed ∧
      compileRetainedNativeRow? config perf arity bitmaps retained =
        some (WordPayloads.wordsToNat typed, compiled.2) ∧
      productionToHolProg (WordPayloads.natToWords width (WordPayloads.wordsToNat typed)) =
        some compiled.1 ∧
      WordPayloads.Bounded width (WordPayloads.wordsToNat typed) := by
  obtain ⟨native, decoded, encoding, decoding, supported⟩ :=
    retainedNativeDecoderDomain copy dead unreach ssa label parameters source retained produced input
  obtain ⟨typed, image⟩ := compileProgNativeOutputImage config perf native decoded decoding
    supported arity cakeRiscVRegisterCount bitmaps
  refine ⟨native, typed, encoding, ?_⟩
  dsimp only
  rw [compileProgNativeRemoveMustTerminate]
  refine ⟨image, ?_, ?_, WordPayloads.bounded_wordsToNat typed⟩
  · simp only [compileRetainedNativeRow?, bind, pure, encoding, Option.bind_some,
      compileProgNativeRemoveMustTerminate, image]
  · rw [WordPayloads.natToWords_wordsToNat]
    exact productionToHolProg_of_holProgToProduction _ typed image

/-- The real source-row boundary supplies all native input conventions and
decoding guards. Every converted output field and payload bound is derived
from that source row and the observed native-copy allocator branch. -/
theorem panToWordRowNativeOutput {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions)
    (config : AsmConfigExact width) (perf : Bool)
    (bitmaps : AppList (BitVec width) × Nat)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label
      (wordSsaAbiParameters arity) (wordBeforeSsaAllocatorBody body) = some output) :
    ∃ (retained : CakeAllocationWithColour (BitVec width))
      (native : WordLangProgHOL (BitVec width)) (typed : StackProg (BitVec width)),
      retained.toLegacy = output ∧
      wordLangProgToHOL retained.colouredProgram = some native ∧
      let compiled := compileProgNative config perf (WordRemove.removeMustTerminate native)
        arity cakeRiscVRegisterCount bitmaps
      holProgToProduction compiled.1 = some typed ∧
      compileRetainedNativeRow? config perf arity bitmaps retained =
        some (WordPayloads.wordsToNat typed, compiled.2) ∧
      productionToHolProg (WordPayloads.natToWords width (WordPayloads.wordsToNat typed)) =
        some compiled.1 ∧
      WordPayloads.Bounded width (WordPayloads.wordsToNat typed) ∧
      compiled.2.1 =
        let slots := cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) body
        if slots = 0 then 0 else slots + 1 := by
  have input := panToWordRow_input functions label arity body row config output produced
  have accepted := panToWordRow_codec functions label arity body row
  obtain ⟨before, encoded⟩ := Option.isSome_iff_exists.mp
    (wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body accepted)
  unfold cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy at produced
  simp only [encoded] at produced
  obtain ⟨retained, actualRun, same⟩ := Option.map_eq_some_iff.mp produced
  subst output
  obtain ⟨native, typed, encoding, image, converted, inverse, bounded⟩ :=
    retainedNativeRowOutput _ _ _ _ label (wordSsaAbiParameters arity)
      _ retained actualRun input config perf arity bitmaps
  obtain ⟨frameNative, frameEncoding, frame⟩ :=
    ProductionFrameCaller.retainedNativeFrame _ _ _ _ label (wordSsaAbiParameters arity)
      _ retained actualRun input config perf bitmaps body
  have sameNative : native = frameNative := Option.some.inj (encoding.symm.trans frameEncoding)
  subst frameNative
  have count : (wordSsaAbiParameters arity).length = arity := by
    simp only [wordSsaAbiParameters, List.length_map, List.length_range]
  rw [count] at frame
  refine ⟨retained, native, typed, rfl, encoding, image, converted, inverse, bounded, ?_⟩
  rw [compileProgNativeRemoveMustTerminate]
  exact frame

end Flapjack.ProductionBodyImage
