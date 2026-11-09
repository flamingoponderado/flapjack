import Flapjack.CakeParser.Nonterminal
import Flapjack.CakeParser.Tokens
import Flapjack.Misc.Location

/-! CakeML's instantiated grammar parse trees. These declarations specialize
HOL's polymorphic grammar carrier to CakeML and are infrastructure rather
than claims to port its polymorphic datatype or helper theorems. -/
namespace Flapjack.CakeParser
open Flapjack.Misc.Location

/-- HOL's `MMLnonT inf`, with generated nonterminals and numeric auxiliaries. -/
abbrev Rule := Sum Nonterminal Nat

/-- A CakeML grammar tree, retaining terminal or nonterminal leaves and
source spans on every node. -/
inductive ParseTree where
  | leaf : Sum Rule Token → Locs → ParseTree
  | node : Rule → Locs → List ParseTree → ParseTree
  deriving BEq

namespace ParseTree

def location : ParseTree → Locs
  | .leaf _ loc => loc
  | .node _ loc _ => loc

def token : ParseTree → Option Token
  | .leaf (.inr token) _ => some token
  | _ => none

/-- Empty lists have unknown location; otherwise use the first and last
child's source endpoints, including sentinel positions. -/
def listLocation : List ParseTree → Locs
  | [] => unknownLoc
  | first :: rest =>
      let .locs start _ := first.location
      let .locs _ stop := (rest.getLast?.getD first).location
      .locs start stop

def mkNode (rule : Rule) (children : List ParseTree) : ParseTree :=
  .node rule (listLocation children) children

end ParseTree
end Flapjack.CakeParser
