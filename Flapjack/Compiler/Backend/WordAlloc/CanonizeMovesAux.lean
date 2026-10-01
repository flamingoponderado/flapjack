import Flapjack.HolRef

namespace Flapjack.WordAlloc

/-- Literal counting recursion over preference/move pairs. The current group
is emitted even for an empty remainder; arbitrary counters and accumulators
are retained. This helper does not assume sorted input and does not replace
the executed allocator's canonicalization route. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "canonize_moves_aux_def"]
def canonizeMovesAux {α : Type} [DecidableEq α]
    (currentPriority : Nat) (currentMove : α)
    (counter : Nat) : List (Nat × α) →
      List (Nat × Nat × α) → List (Nat × Nat × α)
  | [], accumulator => (counter, currentPriority, currentMove) :: accumulator
  | (priority, move) :: rest, accumulator =>
      if currentMove = move then
        canonizeMovesAux (max currentPriority priority) move (counter + 1) rest accumulator
      else
        canonizeMovesAux priority move 1 rest
          ((counter, currentPriority, currentMove) :: accumulator)

end Flapjack.WordAlloc
