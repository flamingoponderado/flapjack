import Flapjack.Compiler.Backend.WordDepth
import Flapjack.Pancake.Proofs.PanToTarget

/-!
# `word_depth` / `option_lt` direct HOL-parity replay

Kernel replay of the original `max_depth` (`cakeml/compiler/backend/word_depthScript.sml:24-35`)
and `option_lt` (`cakeml/pancake/proofs/pan_to_targetProofScript.sml:1157-1159`)
observations over the exact Lean carriers.

Probe infeasibility (recorded, not hidden): the original-HOL oracle for this
module is `scripts/hol-probes/word_depth_probeScript.sml`, registered in
`scripts/hol-probes/regenerate.sh`. It `load`s the original `word_depthTheory`,
but this checkout's `cakeml/` submodule has no built `.hol/objs` (`preamble.ui`
is absent), so `scripts/hol-probes/regenerate.sh` cannot build the theory in
this tree and no `.out` fixture could be captured without fabricating rows.
The rows below are therefore a kernel-checked replay of the definition's
clauses (Leaf/Unknown/Const/Branch/Call hit/miss/nested and the four
`option_lt` cases); when a built `word_depthTheory` is available, regenerate
the probe, add its `.out`, and replace these expectations with the captured
rows. The sibling `mk_Branch`/`call_graph`/`full_call_graph`/`max_depth_graphs`
probe is tracked by bead `flapjack-28je.2`.
-/

namespace Flapjack.Test.WordDepthParity

open Flapjack.Compiler.Backend.WordDepth
open Flapjack.Pancake.Proofs.PanToTarget

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

/-- Direct replay of the original `option_lt` clauses. -/
def optionLtGuard : Bool :=
  -- option_lt n0 NONE ⇔ T (including NONE NONE)
  optionLt none none &&
  optionLt (some 3) none &&
  -- option_lt NONE (SOME n1) ⇔ F
  !(optionLt none (some 3)) &&
  -- option_lt (SOME n1) (SOME n2) ⇔ n1 < n2
  optionLt (some 3) (some 5) &&
  !(optionLt (some 5) (some 3)) &&
  !(optionLt (some 3) (some 3))

#guard optionLtGuard

/-- Kernel-checked replay of the `option_lt` rows. -/
theorem optionLtGuard_proof : optionLtGuard = true := by
  simp [optionLtGuard, optionLt]

def runChecks : IO Bool := do
  if wordDepthGuard then
    IO.println "PASS word_depth call_tree/max_depth HOL parity"
  else
    IO.println "FAIL word_depth call_tree/max_depth HOL parity"
  if optionLtGuard then
    IO.println "PASS pan_to_target option_lt HOL parity"
  else
    IO.println "FAIL pan_to_target option_lt HOL parity"
  pure (wordDepthGuard && optionLtGuard)

end Flapjack.Test.WordDepthParity
