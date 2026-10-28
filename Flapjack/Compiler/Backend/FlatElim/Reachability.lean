import Flapjack.Compiler.Backend.FlatElim.Analysis
import Flapjack.Misc.Sptree.Map
import Flapjack.Misc.Sptree.Wf
import Flapjack.Misc.Sptree.Subspt

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

/-- A sparse tree has size zero exactly when no key can be looked up. This
also handles noncanonical trees whose branch nodes contain no values. -/
theorem size_eq_zero_iff_lookup_none {α : Type} (tree : Spt α) :
    sptSize tree = 0 ↔ ∀ key, sptLookup key tree = none := by
  induction tree with
  | ln => simp [sptLookup]
  | ls value =>
    constructor
    · simp
    · intro empty
      have := empty 0
      simp [sptLookup] at this
  | bn left right ihLeft ihRight =>
    constructor
    · intro zero
      have lzero : sptSize left = 0 := by simp at zero; omega
      have rzero : sptSize right = 0 := by simp at zero; omega
      have lnone := ihLeft.mp lzero
      have rnone := ihRight.mp rzero
      intro key
      simp [sptLookup, lnone, rnone]
    · intro empty
      have lnone : ∀ key, sptLookup key left = none := by
        intro key
        simpa [sptLookup_left_bn] using empty (2 * key + 2)
      have rnone : ∀ key, sptLookup key right = none := by
        intro key
        simpa [sptLookup_right_bn] using empty (2 * key + 1)
      simp [ihLeft.mpr lnone, ihRight.mpr rnone]
  | bs left value right ihLeft ihRight =>
    constructor
    · simp
    · intro empty
      have := empty 0
      simp [sptLookup] at this

/-- For unit-valued trees, an empty difference has exactly the meaning of
HOL's pointwise `subspt`, including for noncanonical sparse trees. -/
theorem difference_size_zero_iff_subspt (nodes reachable : NumSet) :
    sptSize (sptDifference nodes reachable) = 0 ↔ sptSubspt nodes reachable := by
  rw [size_eq_zero_iff_lookup_none, sptSubsptLookup]
  constructor
  · intro empty key value found
    have noDifference := empty key
    rw [sptLookupDifference] at noDifference
    cases target : sptLookup key reachable with
    | none => simp [target, found] at noDifference
    | some targetValue => cases value; cases targetValue; rfl
  · intro subset key
    rw [sptLookupDifference]
    cases source : sptLookup key nodes with
    | none => simp
    | some value =>
      have target := subset key value source
      simp [target]

/-- Execute the HOL closure iteration with an explicit limit. `none` means the
limit was exhausted before the subset test succeeded. This is infrastructure,
not a port of the total HOL definition: sufficiency of a chosen limit still
requires a proof. -/
def closureFuel : Nat → NumSet → Spt NumSet → Option NumSet
  | 0, _, _ => none
  | fuel + 1, reachable, tree =>
      let nodes := foldUnion .ln (sptInter tree reachable)
      if sptSize (sptDifference nodes reachable) == 0 then some reachable
      else closureFuel fuel (sptUnion reachable nodes) tree

/-- Executable total closure. The target-count fuel is proved sufficient in
`Proofs.Reachability`, which also proves equality with the source-shaped
recursive closure; the fallback cannot be observed. -/
@[hol "HOL/examples/algorithms/spt_closureScript.sml" "closure_spt_def"]
def closureTotal (reachable : NumSet) (tree : Spt NumSet) : NumSet :=
  (closureFuel (sptSize (foldUnion .ln tree) + 1) reachable tree).getD reachable

open Classical in
/-- One fuelled closure step has the same stopping and update conditions as
the HOL closure equation. Fuel exhaustion remains a separate obligation. -/
theorem closureFuel_step (fuel : Nat) (reachable : NumSet) (tree : Spt NumSet) :
    closureFuel (fuel + 1) reachable tree =
      let nodes := foldUnion .ln (sptInter tree reachable)
      if sptSubspt nodes reachable then some reachable
      else closureFuel fuel (sptUnion reachable nodes) tree := by
  classical
  simp only [closureFuel, beq_iff_eq, difference_size_zero_iff_subspt]

/-- Run the elimination algorithm with explicit closure fuel. `none` reports
exhaustion; the dynamic-evaluation guard returns the original program directly. -/
def removeFlatProgFuel (fuel : Nat) (code : List Exp) : Option (List Exp) :=
  if code.any hasEvalDec then some code
  else
    let (roots, tree) := analyseCode code
    (closureFuel fuel roots tree).map (fun reachable => removeUnreachable reachable code)

/-- Total dead-code elimination in the original pass order. Its closure
recurrence is proved in `Proofs.Reachability`; the full cross-language pass
correspondence remains to be reviewed. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "remove_flat_prog_def"]
def removeFlatProgTotal (code : List Exp) : List Exp :=
  if code.any hasEvalDec then code
  else
    let (roots, tree) := analyseCode code
    removeUnreachable (closureTotal roots tree) code

/-- Compatibility entry point for callers of the former bounded pass. -/
def removeFlatProg (code : List Exp) : Option (List Exp) := some (removeFlatProgTotal code)

end Flapjack.Compiler.Backend.FlatElim
