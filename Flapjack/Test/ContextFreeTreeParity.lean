import Flapjack.Misc.Grammar
import Flapjack.CakeParser.ParseTree.Grammar

/-! Examples captured from the pinned HOL context-free grammar script. -/
namespace Flapjack.Test.ContextFreeTreeParity
open Flapjack.Misc.Grammar Flapjack.Misc.Location

private def loc₀ : Locs := .locs (.posn 0 0) (.posn 0 0)
private def loc₂ : Locs := .locs (.posn 0 2) (.posn 0 2)
private def tree : ParseTree Nat Nat Locs :=
  .node (.inl 1, .locs (.posn 0 0) (.posn 0 2))
    [.leaf (.tok 7, loc₀), .leaf (.tok 9, loc₂)]

example : mergeListLocs [.locs (.posn 1 2) (.posn 1 3), .locs (.posn 4 5) (.posn 6 7)] =
    .locs (.posn 1 2) (.posn 6 7) := by
  simp [mergeListLocs, mergeLocs]

example : realFringe tree = [(.tok 7, loc₀), (.tok 9, loc₂)] := by
  simp [tree, realFringe, treesRealFringe]

private def emptyGrammar : Grammar Nat Nat := ⟨.inl 1, Flapjack.HolFiniteMapExact.empty⟩

example : ¬ validPtree emptyGrammar tree := by
  simp [tree, validPtree, emptyGrammar, Flapjack.HolFiniteMapExact.empty]

private def populatedGrammar : Grammar Nat Nat :=
  ⟨.inl 1, Flapjack.HolFiniteMapExact.updateEq Flapjack.HolFiniteMapExact.empty
    (.inl 1, fun production => production = [.tok 7, .tok 9])⟩

example : validPtree populatedGrammar tree := by
  simp [tree, validPtree, populatedGrammar, Flapjack.HolFiniteMapExact.updateEq,
    Flapjack.FUPDATE_HOL, treeHead]

example : Flapjack.CakeParser.ParseTree.toGrammarTree (.leaf (.inr .valT) loc₀) =
    .leaf (.tok .valT, loc₀) := by
  simp [Flapjack.CakeParser.ParseTree.toGrammarTree, Flapjack.CakeParser.ParseTree.toGrammarSymbol]

end Flapjack.Test.ContextFreeTreeParity
