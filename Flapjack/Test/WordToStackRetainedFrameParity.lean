import Flapjack.Compiler.Backend.WordToStack.ProductionFrame

namespace Flapjack.Test.WordToStackRetainedFrameParity
open Flapjack Flapjack.RiscV Flapjack.RiscV.CakeRegAlloc
open Compiler.Backend.WordToStack.Native Compiler.Encoders.Asm

-- Eight same-input frame observations from the original probe. Configuration
-- and performance are arbitrary because neither changes the frame projection.
private theorem frameProjection (conf : AsmConfigExact 64) (perf : Bool)
    (program : WordLangProgHOL (BitVec 64)) (arguments registers : Nat) :
    (compileProgNative conf perf program arguments registers (.list [], 0)).2.1 =
      let demand := max ((maxVarHOL program / 2 + 1) - registers)
        (arguments - registers)
      if demand = 0 then 0 else demand + 1 := by
  simp only [compileProgNative]

example (c : AsmConfigExact 64) :
    (compileProgNative c false .skip 0 22 (.list [],0)).2.1 = 0 := by
  rw [frameProjection]; simp [maxVarHOL]
example (c : AsmConfigExact 64) :
    (compileProgNative c false (.assign 42 (.const 0)) 22 22 (.list [],0)).2.1 = 0 := by
  rw [frameProjection]; simp [maxVarHOL, maxVarExpHOL]
example (c : AsmConfigExact 64) :
    (compileProgNative c false (.assign 44 (.const 0)) 0 22 (.list [],0)).2.1 = 2 := by
  rw [frameProjection]; simp [maxVarHOL, maxVarExpHOL]
example (c : AsmConfigExact 64) :
    (compileProgNative c false (.assign 46 (.const 0)) 0 22 (.list [],0)).2.1 = 3 := by
  rw [frameProjection]; simp [maxVarHOL, maxVarExpHOL]
example (c : AsmConfigExact 64) :
    (compileProgNative c false (.assign 44 (.const 0)) 26 22 (.list [],0)).2.1 = 5 := by
  rw [frameProjection]; simp [maxVarHOL, maxVarExpHOL]
example (c : AsmConfigExact 64) :
    (compileProgNative c false (.assign 46 (.const 0)) 24 22 (.list [],0)).2.1 = 3 := by
  rw [frameProjection]; simp [maxVarHOL, maxVarExpHOL]
example (c : AsmConfigExact 64) :
    (compileProgNative c false .skip 0 0 (.list [],0)).2.1 = 2 := by
  rw [frameProjection]; simp [maxVarHOL]
example (c : AsmConfigExact 64) :
    (compileProgNative c false (.assign 18446744073709551616 (.const 0))
      0 22 (.list [],0)).2.1 = 9223372036854775788 := by
  rw [frameProjection]; simp [maxVarHOL, maxVarExpHOL]

-- Rejection is retained, rather than used to infer a native frame or conversion.
example (c : AsmConfigExact 64) :
    (wordLangProgToHOL (.inst (.arith (.addCarry 0 1 2 3 4)) : WordProg (BitVec 64))).map
      (fun p => (compileProgNative c false p 0 22 (.list [],0)).2.1) = none := rfl

-- Apply the actual-result theorem at arbitrary positive widths, colourings and
-- configurations; this is not an allocator-success or native-output proof.
example {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (h : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output)
    (c : AsmConfigExact width) (perf : Bool) (bm : AppList (BitVec width) × Nat) :
    (wordLangProgToHOL output.colouredProgram).map
      (fun p => (compileProgNative c perf p parameters.length cakeRiscVRegisterCount bm).2.1) =
    (wordLangProgToHOL output.colouredProgram).map
      (fun _ => if output.allocation.nextSpill = 0 then 0 else output.allocation.nextSpill + 1) :=
  retainedAllocator_nativeFrame label parameters program output h c perf bm

end Flapjack.Test.WordToStackRetainedFrameParity
