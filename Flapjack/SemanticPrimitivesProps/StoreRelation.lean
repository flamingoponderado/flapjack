import Flapjack.SemanticPrimitivesHOL
import Batteries.Data.List.Basic

/-! Relation between store entries in the source semantics. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.SemanticPrimitivesHOL

@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "sv_rel_def"]
def storeValueRel {A B : Type} (relation : A → B → Prop) : StoreValue A → StoreValue B → Prop
  | .refv left, .refv right => relation left right
  | .w8array left, .w8array right => left = right
  | .varray left, .varray right => List.Forall₂ relation left right
  | .thunk mode left, .thunk mode' right => mode = mode' ∧ relation left right
  | _, _ => False

end Flapjack.SemanticPrimitivesProps
