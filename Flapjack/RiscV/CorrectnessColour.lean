module

public import Flapjack.RiscV.AllocatorCorrectness

@[expose] public section

/-!
Correctness of applying a register colouring to a small, executable Word
fragment. This is the first whole-program simulation statement for allocator
output: it covers straight-line programs made from `skip`, variable-to-
variable assignments, and sequencing.
-/

namespace Flapjack.RiscV

def wordColourValid (colour : Nat → Nat) : Prop :=
  ∀ name, name < 32 → colour name < 32

/-! Local checker bridge for one write's live-after conflict row. The generated
    edge list directly connects the destination with each surviving live name,
    so callers no longer provide a separate edge-coverage premise. This is an
    executable list encoding of the relevant `colouring_ok` injectivity
    obligation, not a port of HOL's recursive `colouring_ok` or
    `evaluate_apply_colour`. -/
def wordSingleWriteClashEdges (destination : Nat) (liveAfter : List Nat) :
    List (Nat × Nat) :=
  liveAfter.map (fun current => (destination, current))

end Flapjack.RiscV
