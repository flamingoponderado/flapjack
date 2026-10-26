import Flapjack.Compiler.Backend.FlatElim.Analysis
import Flapjack.Misc.Sptree.Map

/-! Reachability inputs and removal criterion for flatLang elimination.
The bounded closure exposes exhaustion until its bound is proved sufficient. -/

namespace Flapjack.Compiler.Backend.FlatElim
open FlatLang

/-- Union dependency trees, unioning values at keys present in both. -/
@[hol "HOL/examples/algorithms/spt_closureScript.sml" "num_set_tree_union_def"]
def numSetTreeUnion : Spt NumSet → Spt NumSet → Spt NumSet
  | .ln, t => t
  | .ls a, .ln => .ls a
  | .ls a, .ls b => .ls (sptUnion a b)
  | .ls a, .bn l r => .bs l a r
  | .ls a, .bs l b r => .bs l (sptUnion a b) r
  | .bn l r, .ln => .bn l r
  | .bn l r, .ls a => .bs l a r
  | .bn l r, .bn l' r' => .bn (numSetTreeUnion l l') (numSetTreeUnion r r')
  | .bn l r, .bs l' a r' => .bs (numSetTreeUnion l l') a (numSetTreeUnion r r')
  | .bs l a r, .ln => .bs l a r
  | .bs l a r, .ls b => .bs l (sptUnion a b) r
  | .bs l a r, .bn l' r' => .bs (numSetTreeUnion l l') a (numSetTreeUnion r r')
  | .bs l a r, .bs l' b r' =>
      .bs (numSetTreeUnion l l') (sptUnion a b) (numSetTreeUnion r r')

/-- Compute initially reachable globals and global-to-global dependencies. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "analyse_exp_def"]
def analyseExp (e : Exp) : NumSet × Spt NumSet :=
  let locs := findLoc e
  let lookups := findLookups e
  if isPure e then
    (if isHidden e then .ln else locs, sptMap (fun _ => lookups) locs)
  else
    let both := sptUnion locs lookups
    (both, sptMap (fun _ => .ln) both)

/-- Combine two code-analysis results. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "code_analysis_union_def"]
def codeAnalysisUnion (a b : NumSet × Spt NumSet) : NumSet × Spt NumSet :=
  (sptUnion a.1 b.1, numSetTreeUnion a.2 b.2)

/-- Analyse a program in the original right-fold order. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "analyse_code_def"]
def analyseCode : List Exp → NumSet × Spt NumSet
  | [] => (.ln, .ln)
  | e :: es => codeAnalysisUnion (analyseExp e) (analyseCode es)

/-- Keep side-effecting expressions and assignments to reachable globals. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "keep_def"]
def keep (reachable : NumSet) (e : Exp) : Bool :=
  if sptIsEmpty (sptInter (findLoc e) reachable) then !isPure e else true

/-- Filter a program by the result of the reachability analysis. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "remove_unreachable_def"]
def removeUnreachable (reachable : NumSet) (code : List Exp) : List Exp :=
  code.filter (keep reachable)

/-- Dynamic evaluation in a top-level expression disables elimination. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "has_Eval_dec_def"]
def hasEvalDec (e : Exp) : Bool := hasEval e

/-- The original `spt_fold` order specialized to unioning sets. -/
def foldUnion (acc : NumSet) : Spt NumSet → NumSet
  | .ln => acc
  | .ls a => sptUnion a acc
  | .bn l r => foldUnion (foldUnion acc l) r
  | .bs l a r => foldUnion (sptUnion a (foldUnion acc l)) r

/-- Execute the HOL closure iteration with an explicit limit. `none` means the
limit was exhausted before the subset test succeeded. This is infrastructure,
not a port of the total HOL definition: sufficiency of a chosen limit still
requires a proof. -/
def closureFuel : Nat → NumSet → Spt NumSet → Option NumSet
  | 0, _, _ => none
  | fuel + 1, reachable, tree =>
      let nodes := foldUnion .ln (sptInter tree reachable)
      if sptIsEmpty (sptDifference nodes reachable) then some reachable
      else closureFuel fuel (sptUnion reachable nodes) tree

/-- Run the elimination algorithm with explicit closure fuel. `none` reports
exhaustion; the dynamic-evaluation guard returns the original program directly.
The HOL total pass remains unported until closure termination is established. -/
def removeFlatProgFuel (fuel : Nat) (code : List Exp) : Option (List Exp) :=
  if code.any hasEvalDec then some code
  else
    let (roots, tree) := analyseCode code
    (closureFuel fuel roots tree).map (fun reachable => removeUnreachable reachable code)

/-- Run with a limit derived from the number of distinct dependency targets.
Each nonterminal iteration should discover a new target; proving that fact and
that exhaustion is impossible remains necessary for a total HOL port. -/
def removeFlatProg (code : List Exp) : Option (List Exp) :=
  if code.any hasEvalDec then some code
  else
    let (roots, tree) := analyseCode code
    let fuel := sptSize (foldUnion .ln tree) + 1
    (closureFuel fuel roots tree).map (fun reachable => removeUnreachable reachable code)

end Flapjack.Compiler.Backend.FlatElim
