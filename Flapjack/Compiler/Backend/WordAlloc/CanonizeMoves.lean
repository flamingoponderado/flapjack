import Flapjack.Compiler.Backend.WordAlloc.CanonizeSort
import Flapjack.Compiler.Backend.WordAlloc.CanonizeMovesAux

namespace Flapjack.WordAlloc

/-- Literal normalization, native mllist sorting and counting from HOL.
The grouping helper emits groups in reverse sorted order. The executed
allocator calls this definition through its checked move-list adapter. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "canonize_moves_def"]
def canonizeMoves (moves : List (Nat × (Nat × Nat))) :
    List (Nat × Nat × (Nat × Nat)) :=
  let normalized := moves.map fun (priority, (x, y)) =>
    if x ≤ y then (priority, (x, y)) else (priority, (y, x))
  let sorted := sortCanonizeMoves normalized
  match sorted with
  | [] => []
  | (priority, move) :: rest => canonizeMovesAux priority move 1 rest []

end Flapjack.WordAlloc
