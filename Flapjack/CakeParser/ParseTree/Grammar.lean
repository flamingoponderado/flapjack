module

public import Flapjack.CakeParser.ParseTree
public import Flapjack.Misc.Grammar

@[expose] public section

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

/-- Translate a generic grammar leaf symbol back to the specialized PEG symbol. -/
def ofGrammarSymbol : Misc.Grammar.Symbol Token Nonterminal → Sum Rule Token
  | .tok token => .inr token
  | .nt rule => .inl rule

mutual
/-- Translate a generic HOL-shaped tree back to the executable PEG tree. -/
def ofGrammarTree :
    Misc.Grammar.ParseTree Token Nonterminal Misc.Location.Locs → CakeParser.ParseTree
  | .leaf (symbol, loc) => .leaf (ofGrammarSymbol symbol) loc
  | .node (rule, loc) children => .node rule loc (ofGrammarTrees children)
termination_by tree => sizeOf tree

/-- Flapjack helper for translating a list of generic trees back. -/
def ofGrammarTrees :
    List (Misc.Grammar.ParseTree Token Nonterminal Misc.Location.Locs) →
      List CakeParser.ParseTree
  | [] => []
  | tree :: rest => ofGrammarTree tree :: ofGrammarTrees rest
termination_by trees => sizeOf trees
end

/-- The two leaf-symbol translations are mutually inverse. -/
theorem ofGrammarSymbol_toGrammarSymbol (symbol : Sum Rule Token) :
    ofGrammarSymbol (toGrammarSymbol symbol) = symbol := by
  cases symbol with
  | inl rule => rfl
  | inr token => rfl

/-- The two leaf-symbol translations are mutually inverse in the other order. -/
theorem toGrammarSymbol_ofGrammarSymbol (symbol : Misc.Grammar.Symbol Token Nonterminal) :
    toGrammarSymbol (ofGrammarSymbol symbol) = symbol := by
  cases symbol with
  | tok token => rfl
  | nt rule => rfl

/-- Translating a specialized tree to the generic carrier and back is the
    identity. -/
theorem ofGrammarTree_toGrammarTree (tree : CakeParser.ParseTree) :
    ofGrammarTree (toGrammarTree tree) = tree :=
  CakeParser.ParseTree.rec
    (motive_1 := fun tree => ofGrammarTree (toGrammarTree tree) = tree)
    (motive_2 := fun trees => ofGrammarTrees (toGrammarTrees trees) = trees)
    (fun symbol loc => by
      simp [toGrammarTree, ofGrammarTree, ofGrammarSymbol_toGrammarSymbol])
    (fun rule loc children ih => by
      simp [toGrammarTree, ofGrammarTree, ih])
    (by simp [toGrammarTrees, ofGrammarTrees])
    (fun head tail ihHead ihTail => by
      simp [toGrammarTrees, ofGrammarTrees, ihHead, ihTail])
    tree

/-- Translating a generic tree to the executable carrier and back is the
    identity. -/
theorem toGrammarTree_ofGrammarTree
    (tree : Misc.Grammar.ParseTree Token Nonterminal Misc.Location.Locs) :
    toGrammarTree (ofGrammarTree tree) = tree :=
  Misc.Grammar.ParseTree.rec
    (motive_1 := fun tree => toGrammarTree (ofGrammarTree tree) = tree)
    (motive_2 := fun trees => toGrammarTrees (ofGrammarTrees trees) = trees)
    (fun payload => by
      obtain ⟨symbol, loc⟩ := payload
      simp [ofGrammarTree, toGrammarTree, toGrammarSymbol_ofGrammarSymbol])
    (fun payload children ih => by
      obtain ⟨rule, loc⟩ := payload
      simp [ofGrammarTree, toGrammarTree, ih])
    (by simp [ofGrammarTrees, toGrammarTrees])
    (fun head tail ihHead ihTail => by
      simp [ofGrammarTrees, toGrammarTrees, ihHead, ihTail])
    tree
