import Flapjack.CakeParser.CfgGrammar
import Flapjack.CakeParser.ParseTree.Grammar

/-! A decidable check for the generated grammar on executable PEG trees. This
checks the generated table; it does not prove the table equals HOL `cmlG` or
that every successful PEG evaluation passes the check. -/
namespace Flapjack.CakeParser.CfgValidation
open Flapjack.Misc.Grammar Flapjack.CakeParser.CfgGrammar

/-- The generic grammar symbol at the root of a specialized PEG tree. -/
def headSymbol : CakeParser.ParseTree → Symbol Token Nonterminal
  | .leaf symbol _ => ParseTree.toGrammarSymbol symbol
  | .node rule _ _ => .nt rule

mutual
/-- Check every node against the generated context-free production table. -/
def validTree : CakeParser.ParseTree → Bool
  | .leaf _ _ => true
  | .node (.inr _) _ _ => false
  | .node (.inl name) _ children =>
    (productions name).any (fun p => matchesProduction p (children.map headSymbol)) && validTrees children
termination_by tree => sizeOf tree

/-- Flapjack helper checking every tree in a list. -/
def validTrees : List CakeParser.ParseTree → Bool
  | [] => true
  | tree :: rest => validTree tree && validTrees rest
termination_by trees => sizeOf trees
end

/-- Conversion of a tree list is pointwise conversion. -/
theorem toGrammarTrees_eq_map (trees : List CakeParser.ParseTree) :
    ParseTree.toGrammarTrees trees = trees.map ParseTree.toGrammarTree := by
  induction trees with
  | nil => simp [ParseTree.toGrammarTrees]
  | cons tree rest ih => simp [ParseTree.toGrammarTrees, ih]

/-- Root symbols agree under the PEG-to-grammar conversion. -/
theorem head_toGrammar (tree : CakeParser.ParseTree) :
    treeHead (ParseTree.toGrammarTree tree) = headSymbol tree := by
  cases tree with
  | leaf symbol loc => cases symbol <;> simp [ParseTree.toGrammarTree, treeHead, headSymbol]
  | node rule loc children => simp [ParseTree.toGrammarTree, treeHead, headSymbol]

mutual
/-- The executable check agrees with generic tree validity for the generated
grammar, for every specialized PEG tree. -/
theorem validTree_iff (tree : CakeParser.ParseTree) :
    validTree tree = true ↔ validPtree cmlGrammar (ParseTree.toGrammarTree tree) := by
  cases tree with
  | leaf symbol loc => simp [validTree, ParseTree.toGrammarTree, validPtree]
  | node rule loc children =>
    cases rule with
    | inr aux => simp [validTree, ParseTree.toGrammarTree, validPtree, lookup_auxiliary]
    | inl name =>
      have childrenIh := validTrees_iff children
      simp [validTree, ParseTree.toGrammarTree, validPtree, lookup_nonterminal,
        toGrammarTrees_eq_map, List.map_map, Function.comp_def, head_toGrammar, childrenIh]
termination_by sizeOf tree

/-- Flapjack list case of the generated-grammar validation equivalence. -/
theorem validTrees_iff (trees : List CakeParser.ParseTree) :
    validTrees trees = true ↔
      ∀ tree, tree ∈ trees → validPtree cmlGrammar (ParseTree.toGrammarTree tree) := by
  cases trees with
  | nil => simp [validTrees]
  | cons tree rest =>
    have treeIh := validTree_iff tree
    have restIh := validTrees_iff rest
    simp [validTrees, treeIh, restIh]
termination_by sizeOf trees
end

end Flapjack.CakeParser.CfgValidation
