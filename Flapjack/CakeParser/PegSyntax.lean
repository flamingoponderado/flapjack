import Flapjack.CakeParser.PegActions
import Flapjack.CakeParser.PegChecks

/-! First-order syntax for the CakeML PEG. -/
namespace Flapjack.CakeParser.PegSyntax
open Flapjack.Basis.Pure.MlString PegActions PegChecks

@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "tok_map"]
inductive TokenMap where
  | leaf | empty | bindNT : Rule → TokenMap

@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "pegsym_fo"]
inductive PegExpr where
  | empty : List ParseTree → PegExpr
  | any : TokenMap → PegExpr
  | token : TokenCheck → TokenMap → PegExpr
  | nt : Rule → Unary → PegExpr
  | seq : PegExpr → PegExpr → Binary → PegExpr
  | choice : PegExpr → PegExpr → PegExpr
  | repeat : PegExpr → PegExpr
  | not : PegExpr → List ParseTree → PegExpr
  | error : List HolChar → PegExpr

end Flapjack.CakeParser.PegSyntax
