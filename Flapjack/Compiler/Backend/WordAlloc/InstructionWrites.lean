import Flapjack.Pancake.WordLang

namespace Flapjack.WordAlloc

/-- Literal instruction write sets. Load16 and all unlisted instructions use
the source catchall, yielding LN. FP comparisons write integer registers;
FPMovToReg writes only its first register at width 64 and both otherwise.
This proof-side port does not replace the executed caller yet. -/
-- riscv-mi: integer-only specialization of the referenced HOL declaration.

def getWritesInst {width : Nat} [NeZero width] :
    WordLangInst (BitVec width) → NumSet
  | .const r _ => sptInsert r () .ln
  | .arith (.binop _ r _ _)
  | .arith (.shift _ r _ _)
  | .arith (.div r _ _) => sptInsert r () .ln
  | .arith (.addCarry r1 _ _ r4)
  | .arith (.addOverflow r1 _ _ r4)
  | .arith (.subOverflow r1 _ _ r4) => sptInsert r4 () (sptInsert r1 () .ln)
  | .arith (.longMul r1 r2 _ _)
  | .arith (.longDiv r1 r2 _ _ _) => sptInsert r2 () (sptInsert r1 () .ln)
  | .mem .load r (.addr _ _)
  | .mem .load32 r (.addr _ _)
  | .mem .load8 r (.addr _ _) => sptInsert r () .ln
  | _ => .ln

end Flapjack.WordAlloc
