import Flapjack.Compiler.Backend.WordAlloc.ProductionMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionNormalizedMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionCopyMemoryGuard
import Flapjack.Compiler.Backend.WordCopy.Production

namespace Flapjack.WordAlloc

open RiscV Compiler.Backend.WordCopy

/-- Native copy rewriting retains the memory opcode for every instruction and
copy state. This is a Flapjack runtime-domain invariant, with no HOL original. -/
theorem nativeCopyInstructionMemoryGuard {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (state : CopyState) :
    nativeMemorySupported (copyPropInst instruction state).1 =
      nativeMemorySupported (.inst instruction) := by
  cases instruction <;> simp [copyPropInst, nativeMemorySupported]
  case arith operation =>
    cases operation <;> simp [nativeMemorySupported]
    all_goals split <;> rfl
  case mem operator destination address =>
    cases address
    cases operator <;> simp [nativeMemorySupported]

/-- Whole native copy propagation retains the additional runtime memory guard,
including both call continuations. No guard success or output correspondence
is assumed. This production invariant has no separate HOL declaration. -/
theorem nativeCopyProgramMemoryGuard {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (state : CopyState) :
    nativeMemorySupported (copyPropProg program state).1 =
      nativeMemorySupported program := by
  fun_induction copyPropProg program state
  all_goals try simp_all only [nativeMemorySupported]
  all_goals try exact nativeCopyInstructionMemoryGuard _ _
  all_goals try simp_all [nativeMemorySupported]

/-- The actual fixed-width copy adapter preserves the complete allocator memory
guard, including its rejected-input fallback. This unconditional implementation
correspondence has no HOL original and supplies no successful-allocation or
desired-output premise. -/
theorem nativeCopyWrapperMemoryGuard {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) :
    allocatorMemorySupported (wordCopyPropViaHOL program) =
      allocatorMemorySupported program := by
  cases encoded : wordLangProgToHOL program with
  | none =>
      rw [wordCopyPropViaHOL_rejected program encoded]
      exact copyWrapperMemoryGuard program
  | some native =>
      obtain ⟨output, decoded, same⟩ := wordCopyPropViaHOL_sourceNative program native encoded
      rw [same]
      calc
        allocatorMemorySupported output = nativeMemorySupported (copyProp native) :=
          decodedMemoryGuard _ output decoded
        _ = nativeMemorySupported native := nativeCopyProgramMemoryGuard native emptyEq
        _ = allocatorMemorySupported program := memoryGuardProgram_production program native encoded

end Flapjack.WordAlloc
