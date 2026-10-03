import Flapjack.Compiler.Backend.WordAlloc.ProductionRemoveDead
import Flapjack.Compiler.Backend.WordAlloc.ProductionNormalizedMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionDeadFallbackMemoryGuard

namespace Flapjack.WordAlloc

/-- Native deletion retains the extra production memory domain for arbitrary
backward liveness and store state. This infrastructure has no HOL original;
it does not add a premise to the HOL allocation correctness theorem. -/
theorem nativeDeadMemoryGuard {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (live : NumSet)
    (nlive : List WordStoreHOL) (loops : List (NumSet × NumSet))
    (supported : nativeMemorySupported program = true) :
    nativeMemorySupported (removeDead program live nlive loops).1 = true := by
  fun_induction wordLangProgNormalizeCutsets program generalizing live nlive loops
  case case6 store value =>
    cases value <;> simp [removeDead, nativeMemorySupported]
    split <;> simp [nativeMemorySupported]
  case case9 returns target arguments handler ihReturns ihHandler =>
    rcases returns with _ | ⟨values, sets, body, l1, l2⟩ <;>
      rcases handler with _ | ⟨exception, continuation, h1, h2⟩ <;>
      simp_all [removeDead, nativeMemorySupported]
  all_goals try simp_all [removeDead, nativeMemorySupported]
  all_goals repeat' (split <;> simp_all [nativeMemorySupported])

/-- Complete native cleanup guard preservation, not a HOL semantic theorem. -/
theorem nativeRemoveDeadMemoryGuard {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width))
    (supported : nativeMemorySupported program = true) :
    nativeMemorySupported (removeDeadProg program) = true := by
  exact nativeDeadMemoryGuard program .ln [] [] supported

/-- Both successful native decoding and the actual broad fallback retain
input memory support in the executed router. No target result is assumed.
This is Flapjack production-domain infrastructure with no HOL original. -/
theorem routedRemoveDeadMemoryGuard {width : Nat} [NeZero width]
    (program : WordProg (BitVec width))
    (supported : RiscV.allocatorMemorySupported program = true) :
    RiscV.allocatorMemorySupported (RiscV.wordRemoveDeadProgramViaHOL program) = true := by
  unfold RiscV.wordRemoveDeadProgramViaHOL
  cases encoded : wordLangProgToHOL program with
  | none =>
      simpa [encoded] using removeDeadFallbackMemoryGuard program supported
  | some native =>
      have inputGuard := memoryGuardProgram_production program native encoded
      have outputGuard := nativeRemoveDeadMemoryGuard native (inputGuard.trans supported)
      cases decoded : wordLangProgFromHOL (removeDeadProg native) with
      | none =>
          simpa [encoded, decoded] using removeDeadFallbackMemoryGuard program supported
      | some result =>
          have guard := decodedMemoryGuard _ result decoded
          simpa [encoded, decoded] using guard.trans outputGuard

end Flapjack.WordAlloc
