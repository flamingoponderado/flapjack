import Flapjack.Pancake.WordLang

namespace Flapjack.WordAlloc

/-- Literal instruction write sets. Load16 and all unlisted instructions use
the source catchall, yielding LN. FP comparisons write integer registers;
FPMovToReg writes only its first register at width 64 and both otherwise.
This proof-side port does not replace the executed caller yet. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_writes_inst_def"
  (words_as_type_indexed_bitvec)]
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
  | .fp (.fpLess r _ _)
  | .fp (.fpLessEqual r _ _)
  | .fp (.fpEqual r _ _) => sptInsert r () .ln
  | .fp (.fpMovToReg r1 r2 _) =>
      if width = 64 then sptInsert r1 () .ln
      else sptInsert r2 () (sptInsert r1 () .ln)
  | _ => .ln

end Flapjack.WordAlloc
