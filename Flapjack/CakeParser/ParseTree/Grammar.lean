import Flapjack.CakeParser.ParseTree
import Flapjack.Misc.Grammar

/-! Flapjack conversion between the executable CakeML PEG tree and the
generic HOL-shaped grammar tree. Parser validity and grammar correspondence
remain to be proved. -/
namespace Flapjack.CakeParser.ParseTree

/-- Translate a specialized PEG leaf symbol to the generic grammar symbol. -/
def toGrammarSymbol : Sum Rule Token → Misc.Grammar.Symbol Token Nonterminal
  | .inl rule => .nt rule
  | .inr token => .tok token

mutual
/-- Translate a complete specialized tree while retaining every location. -/
def toGrammarTree : CakeParser.ParseTree → Misc.Grammar.ParseTree Token Nonterminal Misc.Location.Locs
  | .leaf symbol loc => .leaf (toGrammarSymbol symbol, loc)
  | .node rule loc children => .node (rule, loc) (toGrammarTrees children)
termination_by tree => sizeOf tree

/-- Flapjack helper for translating a list of specialized trees. -/
def toGrammarTrees : List CakeParser.ParseTree → List (Misc.Grammar.ParseTree Token Nonterminal Misc.Location.Locs)
  | [] => []
  | tree :: rest => toGrammarTree tree :: toGrammarTrees rest
termination_by trees => sizeOf trees
end

/-- The conversion preserves the location at each tree root. -/
theorem toGrammarTree_location (tree : CakeParser.ParseTree) :
    Misc.Grammar.treeLoc (toGrammarTree tree) = tree.location := by
  cases tree <;> simp [toGrammarTree, Misc.Grammar.treeLoc, location]

end Flapjack.CakeParser.ParseTree
