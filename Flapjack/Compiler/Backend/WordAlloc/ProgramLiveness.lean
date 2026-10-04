import Flapjack.Compiler.Backend.WordAlloc.Expressions
import Flapjack.Compiler.Backend.WordAlloc.Instructions

namespace Flapjack.WordAlloc

/-- Literal source insertion of the head after recursively inserting the tail. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "numset_list_insert_def"]
def numsetListInsert : List Nat → NumSet → NumSet
  | [], tree => tree
  | name :: names, tree => sptInsert name () (numsetListInsert names tree)

/-- Full source program liveness over the exact syntax and numeric trees.
All 27 compiled HOL clauses are retained. The repeated StoreConsts source
row is shadowed: the original HOL get_live_def theorem contains only the first
clause, deleting a and b before inserting c and d. Loop bodies and Call
handlers are deliberately not traversed by this definition; their cutsets
and the surrounding loop table supply the required live sets.
The production route is separately tracked on the inventory bead; this
proof-side definition alone does not complete executable allocator liveness. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getLive {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → NumSet → List (NumSet × NumSet) → NumSet
  | .skip, live, _ => live
  | .move _ moves, live, _ =>
      numsetListInsert (moves.map Prod.snd)
        ((moves.map Prod.fst).foldr sptDelete live)
  | .inst instruction, live, _ => getLiveInst instruction live
  | .assign name value, live, _ => sptUnion (getLiveExp value) (sptDelete name live)
  | .get name _, live, _ => sptDelete name live
  | .store address value, live, _ => sptInsert value () (sptUnion (getLiveExp address) live)
  | .seq first second, live, loops => getLive first (getLive second live loops) loops
  | .mustTerminate body, live, loops => getLive body live loops
  | .ite _ left right yes no, live, loops =>
      let merged := sptUnion (getLive yes live loops) (getLive no live loops)
      match right with
      | .reg name => sptInsert name () (sptInsert left () merged)
      | .imm _ => sptInsert left () merged
  | .alloc name cuts, _, _ => sptInsert name () (sptUnion cuts.1 cuts.2)
  | .storeConsts a b c d _, live, _ =>
      sptInsert c () (sptInsert d () (sptDelete a (sptDelete b live)))
  | .install a b c d cuts, _, _ => sptListInsert [a, b, c, d] (sptUnion cuts.1 cuts.2)
  | .codeBufferWrite a b, live, _ => sptListInsert [a, b] live
  | .dataBufferWrite a b, live, _ => sptListInsert [a, b] live
  | .ffi _ a b c d cuts, _, _ =>
      sptInsert a () (sptInsert b () (sptInsert c () (sptInsert d () (sptUnion cuts.1 cuts.2))))
  | .raise name, live, _ => sptInsert name () live
  | .return name names, live, _ => sptInsert name () (numsetListInsert names live)
  | .tick, live, _ => live
  | .locValue name _, live, _ => sptDelete name live
  | .set _ value, live, _ => sptUnion (getLiveExp value) live
  | .opCurrHeap _ destination source, live, _ => sptInsert source () (sptDelete destination live)
  | .shareInst operator name address, live, _ =>
      let sub := getLiveExp address
      if operator = .store ∨ operator = .store8 ∨ operator = .store16 ∨ operator = .store32
      then sptUnion sub (sptInsert name () live)
      else sptUnion sub (sptDelete name live)
  | .loop names _ _, _, _ => names
  | .break index, _, loops => (loops[index]?).map Prod.snd |>.getD .ln
  | .continue index, _, loops => (loops[index]?).map Prod.fst |>.getD .ln
  | .call none _ args _, _, _ => numsetListInsert args .ln
  | .call (some (_, cuts, _)) _ args _, _, _ =>
      sptUnion (sptUnion cuts.1 cuts.2) (numsetListInsert args .ln)
termination_by program _ _ => sizeOf program
decreasing_by all_goals decreasing_trivial

end Flapjack.WordAlloc
