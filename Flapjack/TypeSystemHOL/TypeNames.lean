import Flapjack.TypeSystemHOL.Environments
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-! Semantic type substitutions and source type-name resolution. The source
and representation review of these definitions remains pending. -/
namespace Flapjack.TypeSystemHOL
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL

/-- Flapjack lookup-and-support view for the canonical finite-map carrier. -/
structure TypeSubstBroad where
  lookup : MlString → Option SemanticT
  finiteSupport : ∃ keys : List MlString, ∀ key, lookup key ≠ none → key ∈ keys

namespace TypeSubstBroad

/-- Convert the canonical finite map to its explicit lookup-and-support view. -/
def toBroad (map : HolFiniteMapExact MlString SemanticT) : TypeSubstBroad :=
  ⟨map.lookup, map.finiteSupport⟩

/-- Reconstruct the canonical finite map from its lookup-and-support view. -/
def ofBroad (map : TypeSubstBroad) : HolFiniteMapExact MlString SemanticT :=
  ⟨map.lookup, map.finiteSupport⟩

end TypeSubstBroad

/-- The finite-map parameter's lookup and finite-support codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_typeSubst_subst
    (subst : HolFiniteMapExact MlString SemanticT) (key : MlString) :
    (TypeSubstBroad.ofBroad (TypeSubstBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (TypeSubstBroad.ofBroad (TypeSubstBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    TypeSubstBroad.ofBroad (TypeSubstBroad.toBroad subst) = subst := by
  cases subst
  exact ⟨rfl, rfl, rfl⟩

mutual
@[hol "cakeml/semantics/typeSystemScript.sml" "type_subst_def"
  (fmap_as_finite_support_parameters := [subst])]
def typeSubst (subst : HolFiniteMapExact MlString SemanticT) : SemanticT → SemanticT
  | .var tv => (subst.lookup tv).getD (.var tv)
  | .varDb n => .varDb n
  | .app ts id => .app (typeSubstList subst ts) id
termination_by t => sizeOf t

/-- Flapjack mutual-recursion helper for substituting a list of types. -/
def typeSubstList (subst : HolFiniteMapExact MlString SemanticT) : List SemanticT → List SemanticT
  | [] => []
  | t :: ts => typeSubst subst t :: typeSubstList subst ts
termination_by ts => sizeOf ts
end

mutual
@[hol "cakeml/semantics/typeSystemScript.sml" "check_type_names_def"]
def checkTypeNames (env : TenvAbbrev) : AstT → Bool
  | .atvar _ => true
  | .attup ts => checkTypeNamesList env ts
  | .atfun t₁ t₂ => checkTypeNames env t₁ && checkTypeNames env t₂
  | .atapp ts name =>
    (match nsLookup env name with
     | some (tvs, _) => tvs.length == ts.length
     | none => false) && checkTypeNamesList env ts
termination_by t => sizeOf t

/-- Flapjack mutual-recursion helper for checking a list of source types. -/
def checkTypeNamesList (env : TenvAbbrev) : List AstT → Bool
  | [] => true
  | t :: ts => checkTypeNames env t && checkTypeNamesList env ts
termination_by ts => sizeOf ts
end

/-- Flapjack finite-map construction for HOL's `alist_to_fmap`: updates are
folded from the right, so the first duplicate key is retained. -/
def typeSubstMap (entries : List (MlString × SemanticT)) : HolFiniteMapExact MlString SemanticT :=
  HolFiniteMapExact.updateListEq HolFiniteMapExact.empty entries.reverse

mutual
@[hol "cakeml/semantics/typeSystemScript.sml" "type_name_subst_def"]
def typeNameSubst (env : TenvAbbrev) : AstT → SemanticT
  | .atvar tv => .var tv
  | .attup ts => .app (typeNameSubstList env ts) 9
  | .atfun t₁ t₂ => .app [typeNameSubst env t₁, typeNameSubst env t₂] 4
  | .atapp ts name =>
    let args := typeNameSubstList env ts
    match nsLookup env name with
    | some (tvs, t) => typeSubst (typeSubstMap (tvs.zip args)) t
    | none => .app args 9
termination_by t => sizeOf t

/-- Flapjack mutual-recursion helper for resolving a list of source types. -/
def typeNameSubstList (env : TenvAbbrev) : List AstT → List SemanticT
  | [] => []
  | t :: ts => typeNameSubst env t :: typeNameSubstList env ts
termination_by ts => sizeOf ts
end

end Flapjack.TypeSystemHOL
