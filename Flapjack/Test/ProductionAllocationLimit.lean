import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocationLimit

namespace Flapjack.Test.ProductionAllocationLimit
open Flapjack Flapjack.RiscV.CakeRegAlloc

/-! Kernel checks for the actual counter boundary. These are Flapjack regressions,
not cross-language oracle claims or HOL theorem ports. -/

example : wordSsaSetupParametersFromLimit 21 [0, 2] =
    ({ current := sptToAList (sptFromAList [(2, 25), (0, 21)]), next := 29 }, [21, 25]) := by
  simp [Compiler.Backend.WordAlloc.ssaNextVarRenameExecutable, Compiler.Backend.WordAlloc.nextVarRename, Compiler.Backend.WordAlloc.ssaForceRenameExecutable, Compiler.Backend.WordAlloc.forceRename, Compiler.Backend.WordAlloc.ssaMapKeysExecutable, sptToAList, sptFromAList, sptFoldi, sptInsert, sptLookup, lrNext, wordSsaSetupParametersFromLimit, wordSsaFreshList, wordSsaFresh]

example : wordFullSsaCcTransNativeLimit 2 (.skip : WordProg (BitVec 64)) =
    some ({ current := sptToAList (sptFromAList [(2, 9), (0, 5)]), next := 13 }, [5, 9],
      .seq (.move 1 [(5, 0), (9, 2)]) .skip) := by
  have abi : wordSsaAbiParameters 2 = [0, 2] := by rfl
  rw [wordFullSsaCcTransNativeLimit_eq]
  simp [Compiler.Backend.WordAlloc.ssaNextVarRenameExecutable, Compiler.Backend.WordAlloc.nextVarRename, Compiler.Backend.WordAlloc.ssaForceRenameExecutable, Compiler.Backend.WordAlloc.forceRename, Compiler.Backend.WordAlloc.ssaMapKeysExecutable, sptToAList, sptFromAList, sptFoldi, sptInsert, sptLookup, lrNext, wordLangProgToHOL, wordFullSsaCcTrans, abi,
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
  simp [cakeAllocateWordFunctionAfterDeadWithColourNativeLimit,
    cakeAllocateWordFunctionAfterDeadWithColourFromLimitWith,
    cakeAllocateWordFunctionAfterDeadWithColourWithSsa, RiscV.allocatorMemorySupported]

example {width : Nat} [NeZero width] (count : Nat) (program : WordProg (BitVec width)) :
    wordFullSsaCcTransNativeLimit count program =
      (wordLangProgToHOL program).map (fun _ => wordFullSsaCcTrans count program) :=
  wordFullSsaCcTransNativeLimit_eq count program

-- Codec-rejected inputs keep the complete historical result and failures.
example {width : Nat} [NeZero width] (label : Nat) (parameters : List Nat)
    (program : WordProg (BitVec width)) (rejected : wordLangProgToHOL program = none) :
    cakeAllocateWordFunctionAfterDeadRoutedLimit label parameters program =
      cakeAllocateWordFunctionAfterDead label parameters program :=
  cakeAllocateWordFunctionAfterDeadRoutedLimit_rejected label parameters program rejected

-- Unsupported extension follows its historical compatibility path, rather
-- than becoming a new codec-rejection allocation failure.
example : cakeAllocateWordFunctionAfterDeadRoutedLimit 0 []
    (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 64)) =
    cakeAllocateWordFunctionAfterDead 0 []
      (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 64)) := by
  rfl

-- Codec acceptance does not alter the allocator's separate memory guard.
example : cakeAllocateWordFunctionAfterDeadRoutedLimit 0 []
    (.inst (.mem .load16 4 8) : WordProg (BitVec 64)) = none := by
  simp [cakeAllocateWordFunctionAfterDeadRoutedLimit, wordLangProgToHOL, wordLangInstToHOL,
    cakeAllocateWordFunctionAfterDeadWithColourFromLimitWith,
    cakeAllocateWordFunctionAfterDeadWithColourWithSsa, RiscV.allocatorMemorySupported]

end Flapjack.Test.ProductionAllocationLimit
