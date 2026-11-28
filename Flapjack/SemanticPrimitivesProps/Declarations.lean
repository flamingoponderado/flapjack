module

public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.AstHOL.Syntax
public import Flapjack.NamespaceHOL

@[expose] public section

/-! Constructors introduced by source declarations and their build checks. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL
open Flapjack.SemanticPrimitivesHOL
open Flapjack.NamespaceHOL

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

/-- A successful constructor-arity check makes the constructor buildable. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "do_con_check_build_conv"]
theorem doConCheck_buildConv (envC : Namespace ModN ConN (Nat × Stamp))
    (name : Option (Ident ModN ConN)) (values : List Value) (arity : Nat)
    (checked : doConCheck envC name arity = true) :
    ∃ value, buildConv envC name values = some value := by
  cases name with
  | none => exact ⟨.conv none values, rfl⟩
  | some name =>
    cases lookup : nsLookup envC name with
    | none => simp [doConCheck, lookup] at checked
    | some entry =>
      obtain ⟨expected, stamp⟩ := entry
      exact ⟨.conv (some stamp) values, by simp [buildConv, lookup]⟩

end Flapjack.SemanticPrimitivesProps
