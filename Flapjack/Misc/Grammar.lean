import Flapjack.Misc.Location.Merge
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-! Generic context-free grammar tree carriers and observations, independent
of CakeML's specialized PEG tree. Source and carrier review remains pending. -/
namespace Flapjack.Misc.Grammar
open Flapjack.Misc.Location

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "symbol"]
inductive Symbol (α β : Type) where
  | tok : α → Symbol α β
  | nt : Sum β Nat → Symbol α β

/-- The grammar's HOL finite-map field uses the canonical finite-support
carrier; its values are predicates on production lists. -/
@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "grammar"
  (fmap_as_finite_support := [rules])]
structure Grammar (α β : Type) where
  start : Sum β Nat
  rules : HolFiniteMapExact (Sum β Nat) (List (Symbol α β) → Prop)

/-- Flapjack lookup-and-support view for the grammar's finite map. -/
structure GrammarBroad (α β : Type) where
  start : Sum β Nat
  lookup : Sum β Nat → Option (List (Symbol α β) → Prop)
  finiteSupport : ∃ keys : List (Sum β Nat), ∀ key, lookup key ≠ none → key ∈ keys

namespace GrammarBroad

/-- Forget the canonical wrapper while retaining its support certificate. -/
def toBroad {α β : Type} (g : Grammar α β) : GrammarBroad α β :=
  ⟨g.start, g.rules.lookup, g.rules.finiteSupport⟩

/-- Reconstruct the canonical grammar from its lookup and support view. -/
def ofBroad {α β : Type} (g : GrammarBroad α β) : Grammar α β :=
  ⟨g.start, ⟨g.lookup, g.finiteSupport⟩⟩

end GrammarBroad

/-- The grammar's canonical finite-map representation has a two-way
lookup-and-support roundtrip with its broad view. -/
theorem holFmapAsFiniteSupportWitness {α β : Type} :
    (∀ g : GrammarBroad α β, GrammarBroad.toBroad (GrammarBroad.ofBroad g) = g) ∧
    (∀ g : Grammar α β, GrammarBroad.ofBroad (GrammarBroad.toBroad g) = g) := by
  constructor <;> intro g <;> cases g <;> rfl

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "isTOK_def"]
def isTok {α β : Type} : Symbol α β → Bool
  | .tok _ => true
  | .nt _ => false

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "destTOK_def"]
def destTok {α β loc : Type} : Symbol α β × loc → Option α
  | (.tok tok, _) => some tok
  | (.nt _, _) => none

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "parsetree"]
inductive ParseTree (α β loc : Type) where
  | leaf : Symbol α β × loc → ParseTree α β loc
  | node : Sum β Nat × loc → List (ParseTree α β loc) → ParseTree α β loc

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "ptree_loc_def"]
def treeLoc {α β loc : Type} : ParseTree α β loc → loc
  | .leaf (_, l) => l
  | .node (_, l) _ => l

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "ptree_list_loc_def"]
def treeListLoc {α β : Type} (trees : List (ParseTree α β Locs)) : Locs :=
  mergeListLocs (trees.map treeLoc)

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "ptree_head_def"]
def treeHead {α β loc : Type} : ParseTree α β loc → Symbol α β
  | .leaf (symbol, _) => symbol
  | .node (rule, _) _ => .nt rule

mutual
@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "ptree_fringe_def" 57]
def treeFringe {α β loc : Type} : ParseTree α β loc → List (Symbol α β)
  | .leaf (symbol, _) => [symbol]
  | .node _ children => treesFringe children
termination_by tree => sizeOf tree

/-- Flapjack mutual-recursion helper for flattened tree fringes. -/
def treesFringe {α β loc : Type} : List (ParseTree α β loc) → List (Symbol α β)
  | [] => []
  | tree :: rest => treeFringe tree ++ treesFringe rest
termination_by trees => sizeOf trees
end

mutual
@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "real_fringe_def"]
def realFringe {α β loc : Type} : ParseTree α β loc → List (Symbol α β × loc)
  | .leaf entry => [entry]
  | .node _ children => treesRealFringe children
termination_by tree => sizeOf tree

/-- Flapjack mutual-recursion helper for location-bearing fringes. -/
def treesRealFringe {α β loc : Type} : List (ParseTree α β loc) → List (Symbol α β × loc)
  | [] => []
  | tree :: rest => realFringe tree ++ treesRealFringe rest
termination_by trees => sizeOf trees
end

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "valid_locs_def"]
def validLocs {α β : Type} : ParseTree α β Locs → Prop
  | .leaf _ => True
  | .node (_, loc) children =>
    loc = treeListLoc children ∧ ∀ child, child ∈ children → validLocs child
termination_by tree => sizeOf tree
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
  simp_wf
  omega

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "valid_ptree_def"
  (fmap_as_finite_support := [rules])]
def validPtree {α β loc : Type} (grammar : Grammar α β) : ParseTree α β loc → Prop
  | .leaf _ => True
  | .node (rule, _) children =>
    (∃ productions, grammar.rules.lookup rule = some productions ∧ productions (children.map treeHead)) ∧
      ∀ child, child ∈ children → validPtree grammar child
termination_by tree => sizeOf tree
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
  simp_wf
  omega

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "complete_ptree_def"
  (fmap_as_finite_support := [rules])]
def completePtree {α β loc : Type} (grammar : Grammar α β) (tree : ParseTree α β loc) : Prop :=
  validPtree grammar tree ∧ treeHead tree = .nt grammar.start ∧
    ∀ symbol, symbol ∈ treeFringe tree → isTok symbol = true

@[hol "HOL/examples/formal-languages/context-free/grammarScript.sml" "valid_lptree_def"
  (fmap_as_finite_support := [rules])]
def validLptree {α β : Type} (grammar : Grammar α β) (tree : ParseTree α β Locs) : Prop :=
  validLocs tree ∧ validPtree grammar tree

end Flapjack.Misc.Grammar
