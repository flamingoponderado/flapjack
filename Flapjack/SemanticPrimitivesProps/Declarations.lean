module

public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.AstHOL.Syntax

@[expose] public section

/-! Constructors introduced by source declarations. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL

/-- The constructor names of one type definition. HOL leaves the first two
components of the triple arbitrary, so their types stay independent. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "ctors_of_tdef_def"]
def ctorsOfTypeDef {α β γ δ : Type} (typeDef : β × γ × List (α × δ)) : List α :=
  typeDef.2.2.map Prod.fst

/-- The constructor names introduced by a declaration. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "ctors_of_dec_def"]
def ctorsOfDec : Dec → List ConN
  | .dtype _ typeDefs => (typeDefs.map ctorsOfTypeDef).flatten
  | .dexn _ name _ => [name]
  | _ => []

end Flapjack.SemanticPrimitivesProps
