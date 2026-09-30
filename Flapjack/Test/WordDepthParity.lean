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

/-! ## `mk_Branch` / `call_graph` / `full_call_graph` / `max_depth_graphs` replay

The original-HOL oracle for these definitions is infeasible in this checkout for
the same reason as the `max_depth` probe: `word_depthTheory` is unbuilt and the
probe harness cannot load `preamble`. Rather than fabricate probe rows, the
clauses below are replayed kernel-checked over concrete small programs on the
exact `CallTree` / `WordLangProgHOL` / `Spt` carriers. When a built
`word_depthTheory` is available, regenerate
`scripts/hol-probes/word_depth_probeScript.sml` with these labels and replace
the expectations with the captured rows. -/

/-- Frame-size map `{2 ↦ 5}` for the replay. -/
private def gFrame2 : Flapjack.Spt Nat := Flapjack.sptInsert 2 5 Flapjack.Spt.ln

/-- Frame-size map `{1 ↦ 4}` for the recursive replay. -/
private def gFrameSelf : Flapjack.Spt Nat := Flapjack.sptInsert 1 4 Flapjack.Spt.ln

/-- Empty cut set pair, the exact `WordLangCutsetsHOL` carrier. -/
private def gCuts : Flapjack.WordLangCutsetsHOL := (Flapjack.Spt.ln, Flapjack.Spt.ln)

/-- Replay word type. -/
private abbrev W8 := BitVec 8

/-- Immediate-return program, the body used by the lookup-hit rows. -/
private def pSkip : Flapjack.WordLangProgHOL W8 := .skip

/-- One-entry code map `{2 ↦ (0, Skip)}`. -/
private def funsHit : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8) :=
  Flapjack.sptInsert 2 (0, pSkip) Flapjack.Spt.ln

/-- One-entry code map `{1 ↦ (0, Call NONE (SOME 1) [] NONE)}` for the
    tail-recursive replay. -/
private def funsTailSelf : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8) :=
  Flapjack.sptInsert 1
    (0, (Flapjack.WordLangProgHOL.call none (some 1) [] none : Flapjack.WordLangProgHOL W8))
    Flapjack.Spt.ln

/-- One-entry code map for the returning-call replay
    `{1 ↦ (0, Call (SOME (nil, cuts, Skip, 0, 0)) (SOME 1) [] NONE)}`. -/
private def funsRetSelf : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8) :=
  Flapjack.sptInsert 1
    (0, (Flapjack.WordLangProgHOL.call (some ([], gCuts, pSkip, 0, 0)) (some 1) [] none :
      Flapjack.WordLangProgHOL W8))
    Flapjack.Spt.ln

/-- Two-entry mutual tail-recursive code map
    `{1 ↦ Call NONE (SOME 2) [] NONE, 2 ↦ Call NONE (SOME 1) [] NONE}`. -/
private def funsMutual : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8) :=
  Flapjack.sptInsert 1
    (0, (Flapjack.WordLangProgHOL.call none (some 2) [] none : Flapjack.WordLangProgHOL W8))
    (Flapjack.sptInsert 2
      (0, (Flapjack.WordLangProgHOL.call none (some 1) [] none : Flapjack.WordLangProgHOL W8))
      Flapjack.Spt.ln)

/-- Kernel-checked replay of the `mk_Branch` / `call_graph` /
    `full_call_graph` / `max_depth_graphs` clauses over concrete small
    programs: the `mk_Branch` absorptions, the `call_graph` structural cases,
    the `Call` `dest`/`lookup`/short-circuit/guard/return/handler cases, the
    `full_call_graph` hit/miss and tail- and non-tail-recursive programs, and the
    `max_depth_graphs` empty/frame-hit/frame-miss/recursive rows. -/
def wordDepthGraphGuard : Bool :=
  -- mk_Branch: identity, Leaf absorption on both sides, Unknown absorption on
  -- both sides, and the structural Branch case.
  decide (mkBranch (.leaf : CallTree) .leaf = .leaf) &&
  decide (mkBranch (.unknown : CallTree) .unknown = .unknown) &&
  decide (mkBranch (.leaf : CallTree) (.const 1 .leaf) = .const 1 .leaf) &&
  decide (mkBranch ((.const 1 .leaf) : CallTree) .leaf = .const 1 .leaf) &&
  decide (mkBranch (.unknown : CallTree) (.const 1 .leaf) = .unknown) &&
  decide (mkBranch ((.const 1 .leaf) : CallTree) .unknown = .unknown) &&
  decide (mkBranch ((.const 1 .leaf) : CallTree) (.const 2 .leaf) =
    .branch (.const 1 .leaf) (.const 2 .leaf)) &&
  -- call_graph: default Leaf, Seq of leaves, Seq with Alloc, Alloc, Install,
  -- MustTerminate, Loop, and If.
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      5 [] 0 (.skip : Flapjack.WordLangProgHOL W8) = (.leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      5 [] 0 (.seq .skip .skip : Flapjack.WordLangProgHOL W8) = (.leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      5 [] 0 (.seq (.alloc 7 gCuts) .skip : Flapjack.WordLangProgHOL W8) = (.call 5 .leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      5 [] 0 (.alloc 7 gCuts : Flapjack.WordLangProgHOL W8) = (.call 5 .leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      5 [] 0 (.install 0 0 0 0 gCuts : Flapjack.WordLangProgHOL W8) = (.unknown : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      3 [] 0 (.mustTerminate (.alloc 7 gCuts) : Flapjack.WordLangProgHOL W8) = (.call 3 .leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      3 [] 0 (.loop Flapjack.Spt.ln (.alloc 7 gCuts) Flapjack.Spt.ln : Flapjack.WordLangProgHOL W8) =
    (.call 3 .leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      3 [] 0 (.ite .equal 0 (.reg 0) (.alloc 7 gCuts) .skip : Flapjack.WordLangProgHOL W8) =
    (.call 3 .leaf : CallTree)) &&
  -- call_graph Call cases: dynamic target, tail-call hit, tail-call miss,
  -- short-circuit when the target is already on the stack, guard failure when
  -- the stack list has reached `total`, and the returning-call handler cases.
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      7 [] 0 (.call none (some 9) [] none : Flapjack.WordLangProgHOL W8) = (.unknown : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      7 [] 0 (.call none none [] none : Flapjack.WordLangProgHOL W8) = (.unknown : CallTree)) &&
  decide (callGraph funsHit 7 [] 1 (.call none (some 2) [] none) = (.call 2 .leaf : CallTree)) &&
  decide (callGraph funsHit 7 [2] 1 (.call none (some 2) [] none) = (.leaf : CallTree)) &&
  decide (callGraph funsHit 7 [] 0 (.call none (some 2) [] none) = (.leaf : CallTree)) &&
  decide (callGraph funsHit 1 [] 1 (.call (some ([], gCuts, pSkip, 0, 0)) (some 2) [] none) =
    (.branch (.call 1 (.call 2 .leaf)) (.call 1 .leaf) : CallTree)) &&
  decide (callGraph funsHit 1 [] 1
      (.call (some ([], gCuts, pSkip, 0, 0)) (some 2) [] (some (0, pSkip, 0, 0))) =
    (.branch (.call 1 (.const 3 (.call 2 .leaf))) (.call 1 (.const 3 .leaf)) : CallTree)) &&
  -- full_call_graph: miss, plain hit, tail-recursive and return-recursive
  -- self calls, and mutual tail recursion.
  decide (fullCallGraph 9 (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8)) =
    (.unknown : CallTree)) &&
  decide (fullCallGraph 2 funsHit = (.branch (.call 2 .leaf) .leaf : CallTree)) &&
  decide (fullCallGraph 1 funsTailSelf = (.branch (.call 1 .leaf) .leaf : CallTree)) &&
  decide (fullCallGraph 1 funsRetSelf =
    (.branch (.call 1 .leaf) (.branch (.call 1 (.call 1 .leaf)) (.call 1 .unknown)) : CallTree)) &&
  decide (fullCallGraph 1 funsMutual = (.branch (.call 1 .leaf) (.call 2 .leaf) : CallTree)) &&
  -- max_depth_graphs: empty list, frame hit, frame miss, whole-code miss, and
  -- a recursive self call whose cycle is cut.
  decide (maxDepthGraphs (Flapjack.Spt.ln : Flapjack.Spt Nat) [] []
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8)) = (some 0 : Option Nat)) &&
  decide (maxDepthGraphs gFrame2 [2] []
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8)) funsHit =
    (some 5 : Option Nat)) &&
  decide (maxDepthGraphs (Flapjack.Spt.ln : Flapjack.Spt Nat) [2] []
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8)) funsHit =
    (none : Option Nat)) &&
  decide (maxDepthGraphs (Flapjack.Spt.ln : Flapjack.Spt Nat) [9] []
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8)) = (none : Option Nat)) &&
  decide (maxDepthGraphs gFrameSelf [1] [] funsTailSelf funsTailSelf = (some 4 : Option Nat))

/-- Kernel-checked replay of the call-graph rows. -/
theorem wordDepthGraphGuard_proof : wordDepthGraphGuard = true := by
  simp [wordDepthGraphGuard, mkBranch, callGraph, fullCallGraph, maxDepthGraphs, maxDepth,
    optionMap₂, Flapjack.sptLookup, Flapjack.sptInsert, Flapjack.sptDelete,
    Flapjack.sptMkBN, gFrame2, gFrameSelf, funsHit, funsTailSelf,
    funsRetSelf, funsMutual, pSkip, gCuts]

def runChecks : IO Bool := do
  if wordDepthGuard then
    IO.println "PASS word_depth call_tree/max_depth HOL parity"
  else
    IO.println "FAIL word_depth call_tree/max_depth HOL parity"
  if wordDepthGraphGuard then
    IO.println "PASS word_depth mk_Branch/call_graph/full_call_graph/max_depth_graphs HOL parity"
  else
    IO.println "FAIL word_depth mk_Branch/call_graph/full_call_graph/max_depth_graphs HOL parity"
  if optionLtGuard then
    IO.println "PASS pan_to_target option_lt HOL parity"
  else
    IO.println "FAIL pan_to_target option_lt HOL parity"
  pure (wordDepthGuard && wordDepthGraphGuard && optionLtGuard)

end Flapjack.Test.WordDepthParity
