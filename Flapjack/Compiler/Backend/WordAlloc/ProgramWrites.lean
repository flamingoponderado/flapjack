import Flapjack.Compiler.Backend.WordAlloc.ProgramLiveness
import Flapjack.Compiler.Backend.WordAlloc.InstructionWrites

namespace Flapjack.WordAlloc

/-- Literal program write sets: this is the source's local write operation,
not a recursive collection of writes from subprograms. Compound programs and
all unlisted constructors return LN. Shared Load16 writes its destination,
whereas the instruction-level Load16 uses getWritesInst's source catchall.
The separate production-route obligation remains open. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_writes_def"
  (words_as_type_indexed_bitvec)]
def getWrites {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → NumSet
  | .move _ moves => numsetListInsert (moves.map Prod.fst) .ln
  | .inst instruction => getWritesInst instruction
  | .assign name _
  | .get name _
  | .locValue name _
  | .install name _ _ _ _
  | .opCurrHeap _ name _ => sptInsert name () .ln
  | .storeConsts a b c d _ =>
      sptInsert a () (sptInsert b () (sptInsert c () (sptInsert d () .ln)))
  | .shareInst .load name _
  | .shareInst .load8 name _
  | .shareInst .load16 name _
  | .shareInst .load32 name _ => sptInsert name () .ln
  | _ => .ln

end Flapjack.WordAlloc
