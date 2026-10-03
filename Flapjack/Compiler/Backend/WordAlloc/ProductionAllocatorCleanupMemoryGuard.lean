import Flapjack.Compiler.Backend.WordAlloc.ProductionDecodedSSAMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionDeadNativeMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionCseMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionCopyMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionThreeToTwoMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionUnreachMemoryGuard

namespace Flapjack.WordAlloc
open RiscV

/-- Guard preservation in the exact executed native allocator cleanup order:
reviewed dead routing, CSE, copy, three-to-two, unreachable pruning and the
second reviewed dead routing. The extra runtime-domain predicate is not a
HOL correctness premise; source-image support remains a separate obligation.
This assembly has no HOL original and assumes no desired output support. -/
theorem allocatorCleanupMemoryGuard {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (supported : allocatorMemorySupported program = true) :
    allocatorMemorySupported (wordRemoveDeadProgramViaHOL
      (wordRemoveUnreachableAfterCopy (wordThreeToTwoReg
        (wordCopyProp (wordCseProp (wordRemoveDeadProgramViaHOL program)))))) = true := by
  apply routedRemoveDeadMemoryGuard
  apply unreachMemoryGuard
  rw [threeToTwoMemoryGuard, copyWrapperMemoryGuard]
  apply cseWrapperMemoryGuard
  exact routedRemoveDeadMemoryGuard program supported

/-- The actual decoded native SSA result supplies support for every subsequent
cleanup stage from its accepted source and source guard. The producer equation
identifies the real returned program; no target evaluator result is assumed.
This is Flapjack production-domain correspondence, not a narrowed HOL theorem. -/
theorem sourceSsaAllocatorCleanupMemoryGuard {width : Nat} [NeZero width]
    (count : Nat) (source : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (supported : allocatorMemorySupported source = true)
    (output : WordSsaState × List Nat × WordProg (BitVec width))
    (produced : wordFullSsaCcTransNativeWithStateFromHOL count native = some output) :
    allocatorMemorySupported (wordRemoveDeadProgramViaHOL
      (wordRemoveUnreachableAfterCopy (wordThreeToTwoReg
        (wordCopyProp (wordCseProp (wordRemoveDeadProgramViaHOL output.2.2)))))) = true := by
  apply allocatorCleanupMemoryGuard
  exact (decodedSsaMemoryGuard_production count source native encoded output produced).trans supported

end Flapjack.WordAlloc
