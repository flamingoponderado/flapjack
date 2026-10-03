import Flapjack.Compiler.Backend.WordDepth

/-! Kernel replays of twelve fresh original HOL EVAL rows in word_depth_probe.out.
Lookup misses and Unknown retain NONE; nested calls retain all frame additions. -/

namespace Flapjack.Test.WordDepthParity

open Flapjack.Compiler.Backend.WordDepth

/-- Exact frame map used by the original probe rows (`insert 1 10 (insert 2 20 LN)`). -/
private def fs10 : Flapjack.Spt Nat :=
  Flapjack.sptInsert 1 10 (Flapjack.sptInsert 2 20 Flapjack.Spt.ln)

/-- Direct replay of the original `max_depth` clauses. -/
def wordDepthGuard : Bool :=
  -- leaf
  maxDepth Flapjack.Spt.ln .leaf == some 0 &&
  -- unknown
  maxDepth Flapjack.Spt.ln .unknown == none &&
  -- const_leaf
  maxDepth Flapjack.Spt.ln (.const 5 .leaf) == some 5 &&
  -- nested_const
  maxDepth Flapjack.Spt.ln (.const 3 (.const 4 .leaf)) == some 7 &&
  -- branch_max
  maxDepth Flapjack.Spt.ln (.branch (.const 3 .leaf) (.const 5 .leaf)) == some 5 &&
  -- branch_unknown
  maxDepth Flapjack.Spt.ln (.branch (.const 3 .leaf) .unknown) == none &&
  -- call_hit
  maxDepth fs10 (.call 1 .leaf) == some 10 &&
  -- call_miss
  maxDepth fs10 (.call 7 .leaf) == none &&
  -- call_hit_nested
  maxDepth fs10 (.call 1 (.const 4 .leaf)) == some 14 &&
  -- deep_calls
  maxDepth fs10 (.call 1 (.call 2 (.const 3 .leaf))) == some 33 &&
  -- branch_call
  maxDepth fs10 (.branch (.call 1 .leaf) (.const 2 .leaf)) == some 10 &&
  -- unknown_deep
  maxDepth fs10 (.branch .unknown (.call 1 (.const 9 .leaf))) == none

#guard wordDepthGuard

/-- Kernel-checked replay of the `max_depth` rows. -/
theorem wordDepthGuard_proof : wordDepthGuard = true := by
  simp [wordDepthGuard, maxDepth, optionMap₂, fs10, Flapjack.sptLookup,
    Flapjack.sptInsert]

end Flapjack.Test.WordDepthParity
