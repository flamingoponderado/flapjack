import Flapjack.Compiler.Backend.WordAlloc.CanonizeMovesAux
import Flapjack.Compiler.Backend.WordAlloc.CanonizeSort

namespace Flapjack.WordAlloc

/-- Literal normalization, original sort and reverse-accumulating grouping.
This proof-side port does not replace the executed allocator's existing route. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "canonize_moves_def"]
def canonizeMoves (moves : List (Nat × Nat × Nat)) :
    List (Nat × Nat × Nat × Nat) :=
  let can1 := moves.map fun (priority, (x, y)) =>
    if x ≤ y then (priority, (x, y)) else (priority, (y, x))
  let can2 := sortCanonizeMoves can1
  match can2 with
  | [] => []
  | (priority, move) :: rest => canonizeMovesAux priority move 1 rest []

end Flapjack.WordAlloc
