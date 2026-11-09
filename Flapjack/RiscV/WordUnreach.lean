module

public import Flapjack.Compiler.Backend.WordUnreach
public import Flapjack.RiscV.CakeRegAlloc
public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec

@[expose] public section

/-!
# Cake-shaped unreachable-sequence cleanup

This is the small `word_unreach` boundary from Cake's
`word_unreachScript.sml`: right-associate sequences, discard continuations
after unconditional transfers, and merge adjacent parallel moves.  It runs
after the SSA dead pass and before allocation, where move merging affects the
allocator's preference graph without changing the observable Word program.
-/

namespace Flapjack.RiscV

open Flapjack

def wordUnreachLookup (moves : List (Nat × Nat)) (name : Nat) : Nat :=
  (lookupNatInfo name moves).getD name

def wordUnreachAnub : List (Nat × Nat) → List Nat → List (Nat × Nat)
  | [], _ => []
  | (destination, source) :: moves, seen =>
      if destination ∈ seen then
        wordUnreachAnub moves seen
      else
        (destination, source) :: wordUnreachAnub moves (destination :: seen)
termination_by moves _ => sizeOf moves
decreasing_by all_goals decreasing_trivial

end Flapjack.RiscV
