module

public import Flapjack.CakeParser.ParseTree
public import Flapjack.Misc.Grammar

@[expose] public section

/-! Small list and option helpers of CakeML's executable PEG.

Lean counterparts of `eval_fold_def`, `in_set_def`, `eval_combine_def`,
`merge_err_option_def`, `map_ptree_loc_def` and `map_ptree_loc_thm` in
`cakeml/compiler/parsing/pegexec_cml_foScript.sml`.  HOL's `FLAT` is Lean's
`List.flatten`, HOL's boolean `∨`/`=` are Lean's `||`/`decide`, and
`ptree_loc` is the tagged `treeLoc` on the generic grammar tree.
-/
namespace Flapjack.CakeParser

open Flapjack.Misc.Grammar

/-- Original `eval_fold_def`: concatenate the produced tree lists. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "eval_fold_def"]
def evalFold {α : Type} (vs : List (List α)) : List α := List.flatten vs

/-- Original `in_set_def`: boolean membership. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "in_set_def"]
def inSet {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => decide (x = y) || inSet x ys

/-- Original `eval_combine_def`: unwrap either side of a sum. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "eval_combine_def"]
def evalCombine {α : Type} : α ⊕ α → α
  | .inl x => x
  | .inr y => y

/-- Original `merge_err_option_def`: keep the first defined option, preferring
the second when both are defined. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "merge_err_option_def"]
def mergeErrOption {α : Type} : Option α → Option α → Option α
  | none, none => none
  | none, some x => some x
  | some x, none => some x
  | some _, some y => some y

/-- Original `map_ptree_loc_def`: project every tree's location. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "map_ptree_loc_def"]
def mapPtreeLoc {β γ loc : Type} :
    List (Misc.Grammar.ParseTree β γ loc) → List loc
  | [] => []
  | x :: ts => Misc.Grammar.treeLoc x :: mapPtreeLoc ts

/-- Original `map_ptree_loc_thm`: the projection is `MAP ptree_loc`. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "map_ptree_loc_thm"]
theorem map_eq_mapPtreeLoc {β γ loc : Type} (l : List (Misc.Grammar.ParseTree β γ loc)) :
    List.map Misc.Grammar.treeLoc l = mapPtreeLoc l := by
  induction l with
  | nil => simp [mapPtreeLoc]
  | cons x xs ih => simp [mapPtreeLoc, ih]

end Flapjack.CakeParser
