import Flapjack.Compiler.Backend.WordAlloc.ProductionMemoryGuard
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
  case fp operation =>
    cases operation <;> simp [nativeMemorySupported]

end Flapjack.WordAlloc
