module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Association-list code included in a canonical finite map. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical lookup and finite-support codec for the code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_codeIncludes_code {K V : Type}
    (code : HolFiniteMapExact K V) (key : K) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- Every association-list binding is present in the finite code map.
Key and value types are independent; lookup uses HOL logical equality. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "code_includes_def"
  (fmap_as_finite_support_parameters := [code])]
def codeIncludes {K V : Type} (al : List (K × V)) (code : HolFiniteMapExact K V) : Prop :=
  ∀ key value, logicalAssocLookup key al = some value → code.lookup key = some value

end Flapjack.Compiler.Backend.ClosCall
