import Flapjack.AstHOL.LitOp

/-! CakeML semantic type carrier used by inference. -/
namespace Flapjack.TypeSystemHOL
open Flapjack.Basis.Pure.MlString

@[hol "cakeml/semantics/typeSystemScript.sml" "type_ident"]
abbrev TypeIdent := Nat

@[hol "cakeml/semantics/typeSystemScript.sml" "t"]
inductive SemanticT where
  | var : MlString → SemanticT
  | varDb : Nat → SemanticT
  | app : List SemanticT → TypeIdent → SemanticT
  deriving Repr

end Flapjack.TypeSystemHOL
