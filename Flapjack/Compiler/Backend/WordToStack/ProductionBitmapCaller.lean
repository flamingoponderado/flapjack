import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapTransport
import Flapjack.Compiler.Backend.WordToStack.ProductionGcCutsets

namespace Flapjack.ProductionBitmapCaller
open RiscV RiscV.CakeRegAlloc ProductionGcCutsets ProductionCleanupConventions

/-- Every actual GC live list in the retained program yields exactly the source
bitmap from the actual colouring and actual spill locations. The native input
conventions come from the complete real SSA/cleanup producer invariant; every
live-name location/clash/stack condition is discharged here. This is production
caller infrastructure, not a narrowed HOL semantic theorem. -/
theorem retainedConsumer_liveBitmap {width : Nat} [NeZero width]
    (copy dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some output)
    (input : NativeInput output.program)
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (target : config.isa = .riscv)
    (live : List Nat) (consumed : ∀ name ∈ live, GcName name output.program) :
    let slots := (cakeColourFrameSlots cakeRiscVRegisterCount parameters output.program output.colouring).1
    wordStackLiveBitmapFromLocations (sourceWordStackConfig label output.allocation slots)
      slots width live =
      CakeAlloc.writeBitmap (live.map (CakeAlloc.totalColour output.colouring))
        cakeRiscVRegisterCount slots width := by
  obtain ⟨native, encoded, pre, flat⟩ := input.encoded output.program
  obtain ⟨spill, allocator⟩ := allocatorWithCopy_retained copy dead unreach ssa
    label parameters source output produced
  dsimp only
  rw [spill]
  exact ProductionBitmapTransport.sourceAllocator_liveBitmap output.program native encoded config target
    .IRC (wordGetHeuristics 3 label output.program).2 cakeRiscVRegisterCount
    ((wordGetHeuristics 3 label output.program).1.map
      (fun move => (move.priority, (move.left, move.right)))) output.colouring (by simpa only [RegAlloc.Algorithm.toProduction] using allocator)
    label parameters live
    (fun name member => List.mem_append_right _ (consumed name member).variables)
    (fun name member => (consumed name member).clash native encoded)
    (fun name member => (consumed name member).stack native encoded pre)

/-- The caller's actual frame-slot operation uses the retained occupancy;
its argument-area floor is already present in the allocator frame. The
post-remove program argument is unrestricted because this operation ignores it.
No desired frame equation is assumed. -/
theorem retainedConsumer_frameSlots {width : Nat} [NeZero width]
    (copy dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some output)
    (renamedProgram : WordProg (BitVec width)) :
    cakeWordFrameSlots output.allocation parameters renamedProgram =
      (cakeColourFrameSlots cakeRiscVRegisterCount parameters output.program output.colouring).1 := by
  obtain ⟨spill, allocator⟩ := allocatorWithCopy_retained copy dead unreach ssa
    label parameters source output produced
  rw [spill]
  simp only [cakeWordFrameSlots, cakeColourWordSpillState_nextSpill_eq_occupancy,
    cakeColourFrameSlots, Nat.max_assoc, Nat.max_self]

/-- Complete actual source caller supplies the original stack/ABI conventions,
colouring producer, spill locations and physical frame operation. Every name
consumed by the selected source GC live list receives the exact original bit
index. Neither output native conventions, location/clash guards, desired frame
relations nor target runs are assumed. The enclosing full bitmap-state/body
transport after must-terminate removal/fusion is a separate task. -/
theorem sourceRouted_liveBitmap {width : Nat} [NeZero width]
    (label : Nat) (parameters allocatorParameters : List Nat)
    (body : LoopProg (BitVec width))
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (target : config.isa = .riscv)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label allocatorParameters
      (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc label parameters body)) = some output)
    (renamedProgram : WordProg (BitVec width))
    (live : List Nat) (consumed : ∀ name ∈ live, GcName name output.2.2.1) :
    ∃ retained : CakeAllocationWithColour (BitVec width),
      retained.toLegacy = output ∧
      let slots := cakeWordFrameSlots output.2.2.2 allocatorParameters renamedProgram
      wordStackLiveBitmapFromLocations (sourceWordStackConfig label output.2.2.2 slots)
        slots width live =
        CakeAlloc.writeBitmap (live.map (CakeAlloc.totalColour retained.colouring))
          cakeRiscVRegisterCount slots width := by
  have input := sourceAllocator_input label parameters allocatorParameters body config output produced
  obtain ⟨native, encoded, flat⟩ := executedSourceAllocatorInput_nativeFlat label parameters body
  unfold cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy at produced
  simp only [encoded] at produced
  obtain ⟨retained, actualRun, same⟩ := Option.map_eq_some_iff.mp produced
  subst output
  refine ⟨retained, rfl, ?_⟩
  change let slots := cakeWordFrameSlots retained.allocation allocatorParameters renamedProgram
         wordStackLiveBitmapFromLocations (sourceWordStackConfig label retained.allocation slots)
           slots width live =
           CakeAlloc.writeBitmap (live.map (CakeAlloc.totalColour retained.colouring))
             cakeRiscVRegisterCount slots width
  rw [retainedConsumer_frameSlots _ _ _ _ label allocatorParameters _ retained actualRun renamedProgram]
  exact retainedConsumer_liveBitmap _ _ _ _ label allocatorParameters _ retained actualRun
    input config target live consumed

/-- Arbitrary accepted Word rows receive exact physical bitmap indices from
actual selector/SSA/cleanup/colouring/frame producers. The row's input codec
is its genuine producer obligation, and no output convention is assumed. -/
theorem acceptedWordRow_liveBitmap {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (body : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL body).isSome = true)
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (target : config.isa = .riscv)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label parameters
      (wordBeforeSsaAllocatorBody body) = some output)
    (renamedProgram : WordProg (BitVec width))
    (live : List Nat) (consumed : ∀ name ∈ live, GcName name output.2.2.1) :
    ∃ retained : CakeAllocationWithColour (BitVec width),
      retained.toLegacy = output ∧
      let slots := cakeWordFrameSlots output.2.2.2 parameters renamedProgram
      wordStackLiveBitmapFromLocations (sourceWordStackConfig label output.2.2.2 slots)
        slots width live =
        CakeAlloc.writeBitmap (live.map (CakeAlloc.totalColour retained.colouring))
          cakeRiscVRegisterCount slots width := by
  have input := acceptedWordRow_input label parameters body accepted config output produced
  obtain ⟨native, encoded⟩ := Option.isSome_iff_exists.mp
    (wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body accepted)
  unfold cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy at produced
  simp only [encoded] at produced
  obtain ⟨retained, actualRun, same⟩ := Option.map_eq_some_iff.mp produced
  subst output
  refine ⟨retained, rfl, ?_⟩
  change let slots := cakeWordFrameSlots retained.allocation parameters renamedProgram
         wordStackLiveBitmapFromLocations (sourceWordStackConfig label retained.allocation slots)
           slots width live =
           CakeAlloc.writeBitmap (live.map (CakeAlloc.totalColour retained.colouring))
             cakeRiscVRegisterCount slots width
  rw [retainedConsumer_frameSlots _ _ _ _ label parameters _ retained actualRun renamedProgram]
  exact retainedConsumer_liveBitmap _ _ _ _ label parameters _ retained actualRun
    input config target live consumed

/-- At the executed FromWord row producer, the original source syntax supplies
the input codec itself. All selected GC live-name colour/location/frame guards
are derived from the returned native-copy allocation. Only actual row and GC
consumer occurrence remain, not desired target/output relations. -/
theorem panToWordRow_liveBitmap {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions)
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (target : config.isa = .riscv)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label (wordSsaAbiParameters arity)
      (wordBeforeSsaAllocatorBody body) = some output)
    (renamedProgram : WordProg (BitVec width))
    (live : List Nat) (consumed : ∀ name ∈ live, GcName name output.2.2.1) :
    ∃ retained : CakeAllocationWithColour (BitVec width),
      retained.toLegacy = output ∧
      let slots := cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram
      wordStackLiveBitmapFromLocations (sourceWordStackConfig label output.2.2.2 slots)
        slots width live =
        CakeAlloc.writeBitmap (live.map (CakeAlloc.totalColour retained.colouring))
          cakeRiscVRegisterCount slots width :=
  acceptedWordRow_liveBitmap label _ body (panToWordRow_codec functions label arity body row)
    config target output produced renamedProgram live consumed

/-- Actual FromWord row provenance also supplies the subsequent WordRemove
codec guard from the actual new allocator result. Broader rejected-input Word
extensions are outside this source producer and remain explicitly separate. -/
theorem panToWordRow_wordRemove_isSome {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label (wordSsaAbiParameters arity)
      (wordBeforeSsaAllocatorBody body) = some output) :
    (wordRemoveMustTerminateViaHOL? output.2.2.1).isSome = true :=
  wordRemoveMustTerminateViaHOL?_isSome _
    (routedNativeCopyAllocator_programCodec label _ _ output
      (wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body
        (panToWordRow_codec functions label arity body row)) produced)

end Flapjack.ProductionBitmapCaller
