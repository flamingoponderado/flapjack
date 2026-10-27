import Flapjack.CakeParser.CfgValidation

/-! Location preservation between executable PEG trees and the generic HOL
grammar trees. These are Flapjack infrastructure lemmas. -/
namespace Flapjack.CakeParser.CfgLocation
open Flapjack.Misc.Location Flapjack.Misc.Grammar Flapjack.CakeParser.CfgValidation
  Flapjack.CakeParser.CfgGrammar

/-- Merging a nonempty list keeps the first start and final end. -/
theorem mergeListLocs_cons (first : Locs) (rest : List Locs) :
    mergeListLocs (first :: rest) = mergeLocs first (rest.getLast?.getD first) := by
  induction rest with
  | nil => cases first <;> simp [mergeListLocs, mergeLocs]
  | cons next rest ih =>
    cases rest with
    | nil => simp [mergeListLocs]
    | cons after tail =>
      simpa [mergeListLocs] using ih

/-- The executable child-location calculation equals generic HOL merging. -/
theorem grammarTreeListLoc (trees : List CakeParser.ParseTree) :
    treeListLoc (ParseTree.toGrammarTrees trees) = ParseTree.listLocation trees := by
  cases trees with
  | nil => simp [treeListLoc, ParseTree.toGrammarTrees, mergeListLocs, ParseTree.listLocation]
  | cons first rest =>
    simp [treeListLoc, toGrammarTrees_eq_map, List.map_map, Function.comp_def,
      ParseTree.toGrammarTree_location, mergeListLocs_cons, ParseTree.listLocation, mergeLocs]

mutual
/-- Check that each PEG node has the location obtained from its children. -/
def validLocations : CakeParser.ParseTree → Bool
  | .leaf _ _ => true
  | .node _ loc children => decide (loc = ParseTree.listLocation children) && validLocationsList children
termination_by tree => sizeOf tree

/-- Flapjack helper for checking a list of tree locations. -/
def validLocationsList : List CakeParser.ParseTree → Bool
  | [] => true
  | tree :: rest => validLocations tree && validLocationsList rest
termination_by trees => sizeOf trees
end

mutual
/-- The executable location check agrees with generic `validLocs` for every
specialized PEG tree. -/
theorem validLocations_iff (tree : CakeParser.ParseTree) :
    validLocations tree = true ↔ validLocs (ParseTree.toGrammarTree tree) := by
  cases tree with
  | leaf symbol loc => simp [validLocations, ParseTree.toGrammarTree, validLocs]
  | node rule loc children =>
    have childrenIh := validLocationsList_iff children
    have locations : treeListLoc (children.map ParseTree.toGrammarTree) = ParseTree.listLocation children := by
      simpa [toGrammarTrees_eq_map] using grammarTreeListLoc children
    simp [validLocations, ParseTree.toGrammarTree, validLocs, toGrammarTrees_eq_map, locations, childrenIh]
termination_by sizeOf tree

/-- Flapjack list case of the location-validity equivalence. -/
theorem validLocationsList_iff (trees : List CakeParser.ParseTree) :
    validLocationsList trees = true ↔ ∀ tree, tree ∈ trees → validLocs (ParseTree.toGrammarTree tree) := by
  cases trees with
  | nil => simp [validLocationsList]
  | cons tree rest =>
    have treeIh := validLocations_iff tree
    have restIh := validLocationsList_iff rest
    simp [validLocationsList, treeIh, restIh]
termination_by sizeOf trees
end

/-- Check both generated-grammar productions and source locations. -/
def validLocatedTree (tree : CakeParser.ParseTree) : Bool :=
  validTree tree && validLocations tree

/-- The combined executable check is exactly generic located-tree validity
for the generated grammar. This does not establish HOL grammar correspondence. -/
theorem validLocatedTree_iff (tree : CakeParser.ParseTree) :
    validLocatedTree tree = true ↔ validLptree cmlGrammar (ParseTree.toGrammarTree tree) := by
  simp [validLocatedTree, validLptree, validTree_iff, validLocations_iff, and_comm]

end Flapjack.CakeParser.CfgLocation
