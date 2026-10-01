import Flapjack.Compiler.Backend.WordToStack.ProductionAllocatorCodec

namespace Flapjack.Test.WordToStackAllocatorCodecParity
open Flapjack Flapjack.RiscV Flapjack.RiscV.CakeRegAlloc

private def stages (arguments : Nat) (program : WordProg (BitVec 8)) : WordProg (BitVec 8) :=
  wordRemoveDeadProgram (wordRemoveUnreachableAfterCopy (wordThreeToTwoReg
    (wordCopyProp (wordCseProp (wordRemoveDeadProgram
      (wordFullSsaCcTrans arguments program).2.2)))))

-- Complete output observations from the fresh original pre-allocation chain.
private def rows : List Bool :=
  [match stages 0 .skip with | .skip => true | _ => false,
   match stages 0 .tick with | .tick => true | _ => false,
   match stages 2 (.raise 2) with
   | .seq (.move 1 [(2,2)]) (.raise 2) => true | _ => false,
   match stages 2 (.call none (some 7) [0,2] none) with
   | .seq (.move 1 [(0,0),(2,2)]) (.call none (some 7) [0,2] none) => true
   | _ => false]

example : rows = [true,true,true,true] := by
  decide +kernel

-- Accepted input includes memory operators excluded by the allocator guard:
-- codec acceptance alone does not promise successful allocation.
example : (wordLangProgToHOL (.inst (.memOffset .load16 3 5 7) : WordProg (BitVec 8))).isSome = true := by
  decide +kernel
example : allocatorMemorySupported (.inst (.memOffset .load16 3 5 7) : WordProg (BitVec 8)) = false := by
  decide +kernel

-- Genuine rejected input cannot supply the theorem's input-acceptance premise.
example : (wordLangProgToHOL (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 8))).isSome = false := by
  decide +kernel

-- A real allocator success prevents the caller statement from being supported
-- solely by hypothetical outputs. This observes the executed wrapper itself.
example : (cakeAllocateWordFunctionAfterDeadWithColour 0 [] (.skip : WordProg (BitVec 8))).isSome = true := by
  decide +kernel
example : cakeAllocateWordFunctionAfterDeadWithColour 0 []
    (.inst (.memOffset .load16 3 5 7) : WordProg (BitVec 8)) = none := by
  decide +kernel

example {width : Nat} [NeZero width] (label : Nat) (parameters : List Nat)
    (program : WordProg (BitVec width))
    (input : (wordLangProgToHOL program).isSome = true)
    (output : CakeAllocationWithColour (BitVec width))
    (h : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output) :
    ∃ native, wordLangProgToHOL output.colouredProgram = some native :=
  retainedAllocator_colouredCodec label parameters program input output h

end Flapjack.Test.WordToStackAllocatorCodecParity
