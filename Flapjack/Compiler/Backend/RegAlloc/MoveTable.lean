import Flapjack.Compiler.Backend.RegAlloc.SortMoves
import Flapjack.Misc.Sptree.Map

/-!
# reg_alloc move-partner table

Literal ports of `reg_allocScript.sml:1319-1343`: the sptree of prioritised
move partners consulted by the biased colour preferences. Payload types are
independent, as in the original types (`pri_move_insert : α -> num -> β ->
(α # β) list num_map -> ...`). HOL `lookup`/`insert`/`map` are the reviewed
`sptLookup`/`sptInsert`/`sptMap`; no well-formedness premise is imposed. The
executed allocator builds the same table over node-indexed arrays
(`CakeRegAlloc.cakeMovesToSp`/`cakeResortMovesSp`); that correspondence is
separate work.
-/

namespace Flapjack.RegAlloc

/-- Literal `pri_move_insert` (`reg_allocScript.sml:1319-1326`): prepend
`(p, y)` to the partner list of `x`, creating it when absent. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "pri_move_insert_def"]
def priMoveInsert {α β : Type} (p : α) (x : Nat) (y : β) (acc : Spt (List (α × β))) :
    Spt (List (α × β)) :=
  match sptLookup x acc with
  | none => sptInsert x [(p, y)] acc
  | some ls => sptInsert x ((p, y) :: ls) acc

/-- Literal `undir_move_insert` (`reg_allocScript.sml:1328-1331`): record the
move at both endpoints, `y` first. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "undir_move_insert_def"]
def undirMoveInsert {α : Type} (p : α) (x y : Nat) (acc : Spt (List (α × Nat))) :
    Spt (List (α × Nat)) :=
  priMoveInsert p x y (priMoveInsert p y x acc)

/-- Literal `moves_to_sp` (`reg_allocScript.sml:1333-1338`): insert each
`(p, x, y)` move, head first, into the accumulator. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "moves_to_sp_def"]
def movesToSp {α : Type} : List (α × (Nat × Nat)) → Spt (List (α × Nat)) →
    Spt (List (α × Nat))
  | [], acc => acc
  | move :: xs, acc =>
    let (p, x, y) := move
    movesToSp xs (undirMoveInsert p x y acc)

/-- Literal `resort_moves` (`reg_allocScript.sml:1341-1343`): sort every
partner list by the reviewed `sort_moves` and drop the priorities. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "resort_moves_def"]
def resortMoves {α : Type} (acc : Spt (List (Nat × α))) : Spt (List α) :=
  sptMap (fun ls => (sortMoves ls).map Prod.snd) acc

end Flapjack.RegAlloc
