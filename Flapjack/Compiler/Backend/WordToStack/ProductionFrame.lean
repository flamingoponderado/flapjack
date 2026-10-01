import Flapjack.Compiler.Backend.WordToStack.ProductionProgramMaximum
import Flapjack.Compiler.Backend.WordToStack.ProductionColourDomain
import Flapjack.Compiler.Backend.WordToStack.NativePrograms
import Flapjack.RiscV.WordDeadCode
import Flapjack.RiscV.PipelineDiagnostics

namespace Flapjack
open RiscV RiscV.CakeRegAlloc
open Compiler.Backend.WordToStack.Native Compiler.Encoders.Asm

/-- The production caller's argument-area floor is already included in the
actual allocator occupancy. This uses the executed allocation result, not an
assumed frame equation. Flapjack-specific caller infrastructure. -/
theorem retainedAllocator_cakeWordFrameSlots {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (allocated : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output) :
    cakeWordFrameSlots output.allocation parameters output.program =
      output.allocation.nextSpill := by
  have occupancy := cakeAllocateWordFunctionAfterDeadWithColour_frame
    label parameters program output allocated
  simp only [cakeWordFrameSlots, occupancy, Nat.max_assoc, Nat.max_self]

/-- Flapjack caller correspondence, not a HOL theorem port. The actual
retained allocator result supplies the occupancy and checked memory guard.
The partial codec remains explicit: this establishes no successful conversion,
native ABI/configuration correspondence, output equivalence, or executed route.
The native frame formula is the reviewed `compile_prog_def` formula. -/
theorem retainedAllocator_nativeFrame {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (allocated : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output)
    (conf : AsmConfigExact width) (perf : Bool)
    (bitmaps : AppList (BitVec width) × Nat) :
    (wordLangProgToHOL output.colouredProgram).map
      (fun native => (compileProgNative conf perf native parameters.length
        cakeRiscVRegisterCount bitmaps).2.1) =
    (wordLangProgToHOL output.colouredProgram).map
      (fun _ => if output.allocation.nextSpill = 0 then 0
        else output.allocation.nextSpill + 1) := by
  have maximum := wordProgCakeMaxVar_codec output.colouredProgram
  have occupancy := cakeAllocateWordFunctionAfterDeadWithColour_frame
    label parameters program output allocated
  cases encoded : wordLangProgToHOL output.colouredProgram with
  | none => rfl
  | some native =>
      simp only [encoded, Option.map_some, Option.some.injEq] at maximum ⊢
      simp only [compileProgNative]
      rw [maximum, ← occupancy]

/-- The same native frame equation with the actual production frame-slot
function. Neither codec success nor output/ABI equivalence is inferred. -/
theorem retainedAllocator_nativeCallerFrame {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (allocated : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output)
    (conf : AsmConfigExact width) (perf : Bool)
    (bitmaps : AppList (BitVec width) × Nat) :
    (wordLangProgToHOL output.colouredProgram).map
      (fun native => (compileProgNative conf perf native parameters.length
        cakeRiscVRegisterCount bitmaps).2.1) =
    (wordLangProgToHOL output.colouredProgram).map
      (fun _ => let slots := cakeWordFrameSlots output.allocation parameters output.program
        if slots = 0 then 0 else slots + 1) := by
  rw [retainedAllocator_cakeWordFrameSlots label parameters program output allocated]
  exact retainedAllocator_nativeFrame label parameters program output allocated conf perf bitmaps

end Flapjack
