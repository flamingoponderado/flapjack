import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ValueOk

/-! Relocation agreement on well-formed source values. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref)

private def toBroad (refs : HolFiniteMapExact Nat (Ref Value)) : Nat → Option (Ref Value) := refs.lookup
private def ofBroad (lookup : Nat → Option (Ref Value))
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Ref Value) := ⟨lookup, support⟩

/-- Canonical reference-map roundtrip for relocation agreement. -/
theorem holFmapAsFiniteSupportParamWitness_adjustBv_eq_of_ok_refs
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

mutual
/-- Relocations that agree on the reference domain give the same translation
of every value well formed in that domain. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bv_ok_IMP_adjust_bv_eq"
  (fmap_as_finite_support_parameters := [refs])]
theorem adjustBv_eq_of_ok (first : Nat → Nat) (value : Value) (second : Nat → Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (ok : bvOk refs value)
    (agree : ∀ key, refs.lookup key ≠ none → first key = second key) :
    adjustBv first value = adjustBv second value := by
  cases value with
  | refPtr flag key => simpa [adjustBv] using agree key (by simpa [bvOk] using ok)
  | block tag values =>
    simp only [adjustBv, Value.block.injEq, true_and]
    exact adjustValues_eq_of_ok first values second refs (by simpa [bvOk] using ok) agree
  | _ => simp [adjustBv]
termination_by sizeOf value

/-- Flapjack helper lifting relocation agreement over a list of valid values. -/
theorem adjustValues_eq_of_ok (first : Nat → Nat) (values : List Value) (second : Nat → Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (ok : bvOkList refs values)
    (agree : ∀ key, refs.lookup key ≠ none → first key = second key) :
    adjustValues first values = adjustValues second values := by
  cases values with
  | nil => simp [adjustValues]
  | cons value rest =>
    simp only [bvOkList] at ok
    simp only [adjustValues, List.cons.injEq]
    exact ⟨adjustBv_eq_of_ok first value second refs ok.1 agree,
      adjustValues_eq_of_ok first rest second refs ok.2 agree⟩
termination_by sizeOf values
end

/-- Relocation agreement also preserves the complete mapped environment. -/
theorem adjustMap_eq_of_ok (first second : Nat → Nat) (values : List Value)
    (refs : HolFiniteMapExact Nat (Ref Value)) (ok : bvOkList refs values)
    (agree : ∀ key, refs.lookup key ≠ none → first key = second key) :
    values.map (adjustBv first) = values.map (adjustBv second) := by
  simpa [adjustValues_eq_map] using adjustValues_eq_of_ok first values second refs ok agree

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
