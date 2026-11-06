import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
import Flapjack.Pancake.Semantics.CrepSem.HOLState

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

/-- If the larger state is included in code, every binding of the smaller
state is included as well. -/
theorem codeIncludes_of_stateExtends {A K V : Type} (g0 g1 : Spt A × List (K × V))
    (code : HolFiniteMapExact K V) (growth : stateExtends g0 g1)
    (included : codeIncludes g1.2 code) : codeIncludes g0.2 code := by
  intro key value lookup
  exact included key value (growth.2.1 key value lookup)

/-- Extending a finite code map preserves every included binding. -/
theorem codeIncludes_mono {K V : Type} (al : List (K × V))
    (code code' : HolFiniteMapExact K V)
    (growth : ∀ key value, code.lookup key = some value → code'.lookup key = some value)
    (included : codeIncludes al code) : codeIncludes al code' := by
  intro key value lookup
  exact growth key value (included key value lookup)

/-- Installing all code produced by a successful traversal also installs
the bindings present before that traversal. -/
theorem callsListBounded_codeIncludes_initial (fuel : Nat) (es : List ClosLang.Exp)
    (initial final : State) (out : List ClosLang.Exp)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (run : callsListBounded fuel es initial = some (out, final))
    (distinct : (ClosProps.codeLocations es).Nodup)
    (fresh : LabelsFresh (ClosProps.codeLocations es) initial)
    (oldDistinct : (initial.2.map Prod.fst).Nodup)
    (included : codeIncludes final.2 code) : codeIncludes initial.2 code := by
  exact codeIncludes_of_stateExtends initial final code
    (callsListBounded_stateExtends fuel es initial final out run distinct fresh oldDistinct) included

end Flapjack.Compiler.Backend.ClosCall
