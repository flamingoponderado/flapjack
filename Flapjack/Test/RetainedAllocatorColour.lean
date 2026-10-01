import Flapjack.RiscV.WordDeadCode

/-! Kernel applications at the actual BitVec caller boundary. These are
carrier/guard certificates; native program-max correspondence and compiler
simulation remain separate obligations. Original executable output is checked
by the source-to-RISC-V corpus, rather than a second Lean implementation. -/
namespace Flapjack.Test.RetainedAllocatorColour
open Flapjack Flapjack.RiscV Flapjack.RiscV.CakeRegAlloc

example {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (h : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output) :
    output.allocation.nextSpill =
      max ((wordProgCakeMaxVar output.colouredProgram / 2 + 1) - cakeRiscVRegisterCount)
        (parameters.length - cakeRiscVRegisterCount) ∧
      allocatorMemorySupported output.program = true :=
  ⟨cakeAllocateWordFunctionAfterDeadWithColour_frame label parameters program output h,
    cakeAllocateWordFunctionAfterDeadWithColour_output_supported label parameters program output h⟩

example {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (h : cakeAllocateWordFunctionAfterDead label parameters program = some output) :
    ¬ UnsupportedAllocatorMemory program ∧ allocatorMemorySupported output.2.2.1 = true :=
  ⟨cakeAllocateWordFunctionAfterDead_input_safe label parameters program output h,
    cakeAllocateWordFunctionAfterDead_output_supported label parameters program output h⟩

end Flapjack.Test.RetainedAllocatorColour
