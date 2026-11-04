import Flapjack.RiscV.RegAlloc
import Flapjack.RiscV.CakeAllocatorCore

/-!
An oracle-backed entry point for the CakeML-shaped Word allocator.

CakeML accepts an optional externally supplied colouring when it satisfies the
clash-tree, forced-clash, and stack-colour checks.  The graph allocator already
provides the same executable clash-tree oracle and total-colour convention;
this module connects those pieces at the function boundary so a validated
colouring can be consumed by the existing Word pipeline.
-/

namespace Flapjack

open Flapjack.RiscV.CakeAlloc

def wordClashTreeNames : WordClashTree → List Nat
  | .delta writes reads => writes ++ reads
  | .set names => names
  | .branch branchLive thenBranch elseBranch =>
      (match branchLive with
      | none => []
      | some names => names) ++
        wordClashTreeNames thenBranch ++ wordClashTreeNames elseBranch
  | .seq first second => wordClashTreeNames first ++ wordClashTreeNames second
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

/-! Cake's allocator applies `total_colour` to the complete Word program after
    IRC colouring.  Keep this boundary named so callers cannot accidentally
    apply the compressed colour map directly or omit nested handlers/live sets. -/

def wordOracleEdgesSafe (colour : Nat → Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (left, right) :: edges =>
      colour left != colour right && wordOracleEdgesSafe colour edges

def wordOracleStackSafe (colour : Nat → Nat) (stackStart : Nat) :
    List Nat → Bool
  | [] => true
  | name :: names =>
      (if name % 4 == 3 then colour name ≥ stackStart else true) &&
        wordOracleStackSafe colour stackStart names

end Flapjack
