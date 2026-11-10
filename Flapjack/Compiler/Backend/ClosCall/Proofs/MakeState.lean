module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.FiniteMap.DomainExact
public import Flapjack.Misc.Option

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Construct direct-call compiler states from a sparse map and code. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- The code parameter uses the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_makeState_code {B : Type}
    (code : HolFiniteMapExact Nat B) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- Construct the auxiliary code list when every known location has code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "make_g_def"
  (fmap_as_finite_support_parameters := [code])]
noncomputable def makeState {A B : Type} [Nonempty B] (d : Spt A)
    (code : HolFiniteMapExact Nat B) : Option (Spt A × List (Nat × B)) := by
  classical
  exact if Set.image Nat.succ (sptDomain d) ⊆ code.domain then
    some (d, (sptToAList d).map (fun entry => (entry.1 + 1, holThe (code.lookup (entry.1 + 1)))))
  else none

end Flapjack.Compiler.Backend.ClosCall
