import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Native SSA merge moves. The tail runs before looking up the current key in
the resulting maps. Missing or equal names preserve that result; unequal present
names prepend moves and overwrite both maps with the next register. Executed
list-state SSA routing is defined in MergeMovesRoute and used by Allocator;
ProductionMergeMoves proves its codec observations. Full SSA simulation remains
a separate obligation. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "merge_moves_def"]
def mergeMoves (names : List Nat) (leftMap rightMap : Spt Nat) (next : Nat) :
    List (Nat × Nat) × List (Nat × Nat) × Nat × Spt Nat × Spt Nat :=
  match names with
  | [] => ([], [], next, leftMap, rightMap)
  | name :: names =>
    let (leftMoves, rightMoves, next', leftMap', rightMap') :=
      mergeMoves names leftMap rightMap next
    match sptLookup name leftMap', sptLookup name rightMap' with
    | none, _ => (leftMoves, rightMoves, next', leftMap', rightMap')
    | some _, none => (leftMoves, rightMoves, next', leftMap', rightMap')
    | some leftValue, some rightValue =>
      if leftValue = rightValue then
        (leftMoves, rightMoves, next', leftMap', rightMap')
      else
        ((next', leftValue) :: leftMoves, (next', rightValue) :: rightMoves,
          next' + 4, sptInsert name next' leftMap', sptInsert name next' rightMap')

end Flapjack.Compiler.Backend.WordAlloc
