import Flapjack.Compiler.Backend.WordAlloc.InstructionWrites

namespace Flapjack.Test.WordAllocInstructionWritesParity
open WordAlloc

/-- Kernel replay of the same seven original HOL instruction-write inputs
and complete output trees. These are regression observations, not an
independent cross-language equivalence theorem. -/
example : getWritesInst (.const 1 7 : WordLangInst (BitVec 8)) =
    sptInsert 1 () .ln := by decide +kernel

example : getWritesInst (.arith (.addCarry 1 2 3 4) : WordLangInst (BitVec 8)) =
    sptInsert 4 () (sptInsert 1 () .ln) := by decide +kernel

example : getWritesInst (.arith (.longDiv 1 2 3 4 5) : WordLangInst (BitVec 8)) =
    sptInsert 2 () (sptInsert 1 () .ln) := by decide +kernel

example : getWritesInst (.mem .load16 1 (.addr 2 0) : WordLangInst (BitVec 8)) =
    .ln := by decide +kernel

end Flapjack.Test.WordAllocInstructionWritesParity
