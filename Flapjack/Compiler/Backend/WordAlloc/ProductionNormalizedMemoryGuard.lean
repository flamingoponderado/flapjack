import Flapjack.Compiler.Backend.WordAlloc.ProductionMemoryGuard

namespace Flapjack.WordAlloc

/-- Cutset reconstruction does not alter the additional production memory
restriction. This is Flapjack carrier infrastructure with no HOL original;
it assumes neither successful allocation nor guard success. -/
theorem normalizedMemoryGuard {width : Nat}
    (program : WordLangProgHOL (BitVec width)) :
    nativeMemorySupported (wordLangProgNormalizeCutsets program) =
      nativeMemorySupported program := by
  fun_induction wordLangProgNormalizeCutsets program
  case case9 returns target arguments handler ihReturns ihHandler =>
    rcases returns with _ | ⟨values, sets, body, l1, l2⟩ <;>
      rcases handler with _ | ⟨exception, continuation, h1, h2⟩ <;>
      simp_all [nativeMemorySupported]
  all_goals first | simp_all [nativeMemorySupported] | rfl

/-- Every successful native decoder retains the exact production memory guard.
The equation binds the actual decoded program; it supplies no target evaluation
or assumed support fact. This correspondence has no HOL original. -/
theorem decodedMemoryGuard {width : Nat}
    (native : WordLangProgHOL (BitVec width)) (actual : WordProg (BitVec width))
    (decoded : wordLangProgFromHOL native = some actual) :
    RiscV.allocatorMemorySupported actual = nativeMemorySupported native := by
  have encoded := wordLangProgToHOL_of_fromHOL native actual decoded
  have guard := memoryGuardProgram_production actual _ encoded
  simpa only [normalizedMemoryGuard] using guard.symm

end Flapjack.WordAlloc
