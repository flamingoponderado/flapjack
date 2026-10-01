import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocationLimit

namespace Flapjack.Test.ProductionAllocationLimit
open Flapjack Flapjack.RiscV.CakeRegAlloc

/-! Kernel checks for the actual counter boundary. These are Flapjack regressions,
not cross-language oracle claims or HOL theorem ports. -/

example : wordSsaSetupParametersFromLimit 21 [0, 2] =
    ({ current := [(2, 25), (0, 21)], next := 29 }, [21, 25]) := by
  simp [wordSsaSetupParametersFromLimit, wordSsaFreshList, wordSsaFresh]

example : wordFullSsaCcTransNativeLimit 2 (.skip : WordProg (BitVec 64)) =
    some ({ current := [(2, 9), (0, 5)], next := 13 }, [5, 9],
      .seq (.move 1 [(5, 0), (9, 2)]) .skip) := by
  have abi : wordSsaAbiParameters 2 = [0, 2] := by rfl
  rw [wordFullSsaCcTransNativeLimit_eq]
  simp [wordLangProgToHOL, wordFullSsaCcTrans, abi,
    wordSsaRenameFunctionWithEntry, wordSsaEntryMove, wordSsaRenameFunction,
    wordSsaSetupParameters, wordSsaLimitVar, wordProgCakeMaxVar,
    wordSsaFreshList, wordSsaFresh, wordSsaRenameProgram, wordSsaRenameProgramWithLoops]

example : wordFullSsaCcTransNativeLimit 0
    (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 64)) = none := by rfl

-- Rejection is not hidden by a synthetic native maximum program.
example : cakeAllocateWordFunctionAfterDeadWithColourNativeLimit 0 []
    (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 64)) = none := by rfl

-- The accepted codec does not waive the original ordinary-16-bit memory guard.
example : cakeAllocateWordFunctionAfterDeadWithColourNativeLimit 0 []
    (.inst (.mem .load16 4 8) : WordProg (BitVec 64)) = none := by
  rw [cakeAllocateWordFunctionAfterDeadWithColourNativeLimit_eq]
  simp [cakeAllocateWordFunctionAfterDeadWithColour,
    cakeAllocateWordFunctionAfterDeadWithColourFromLimit, RiscV.allocatorMemorySupported]

example {width : Nat} [NeZero width] (count : Nat) (program : WordProg (BitVec width)) :
    wordFullSsaCcTransNativeLimit count program =
      (wordLangProgToHOL program).map (fun _ => wordFullSsaCcTrans count program) :=
  wordFullSsaCcTransNativeLimit_eq count program

example {width : Nat} [NeZero width] (label : Nat) (parameters : List Nat)
    (program : WordProg (BitVec width)) :
    cakeAllocateWordFunctionAfterDeadNativeLimit label parameters program =
      (wordLangProgToHOL program).bind (fun _ =>
        cakeAllocateWordFunctionAfterDead label parameters program) :=
  cakeAllocateWordFunctionAfterDeadNativeLimit_eq label parameters program

end Flapjack.Test.ProductionAllocationLimit
