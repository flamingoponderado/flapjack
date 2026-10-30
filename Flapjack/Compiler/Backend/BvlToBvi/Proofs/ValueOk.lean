import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Refs
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateRefs
import Flapjack.Compiler.Backend.Semantics.BvlProps.FindCode

/-! Domain monotonicity and list values for BVL-to-BVI well-formedness. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref listToValue)

namespace ValueEvaluationCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ValueEvaluationCarrier

private def toBroad (refs : HolFiniteMapExact Nat (Ref Value)) : Nat → Option (Ref Value) := refs.lookup
private def ofBroad (lookup : Nat → Option (Ref Value))
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Ref Value) := ⟨lookup, support⟩

/-- Canonical reference-map roundtrip for list-value construction. -/
theorem holFmapAsFiniteSupportParamWitness_listToValue_ok_refs
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical reference-map roundtrip for concatenated list values. -/
theorem holFmapAsFiniteSupportParamWitness_listToValue_ok_append_refs
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  exact holFmapAsFiniteSupportParamWitness_listToValue_ok_refs refs key

/-- Canonical reference-map roundtrip for code lookup arguments. -/
theorem holFmapAsFiniteSupportParamWitness_findCode_bvOk_refs
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  exact holFmapAsFiniteSupportParamWitness_listToValue_ok_refs refs key

mutual
/-- Enlarging the reference domain preserves value well-formedness. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bv_ok_SUBSET_IMP"
  (fmap_as_finite_support_relation := [refs, refs2])]
theorem bvOk_domain_mono (refs : HolFiniteMapExact Nat (Ref Value)) (value : Value)
    (refs2 : HolFiniteMapExact Nat (Ref Value))
    (ok : bvOk refs value)
    (subset : ∀ key, refs.lookup key ≠ none → refs2.lookup key ≠ none) :
    bvOk refs2 value := by
  cases value with
  | refPtr flag ptr => simpa [bvOk] using subset ptr (by simpa [bvOk] using ok)
  | block tag values =>
    simpa [bvOk] using bvOkList_domain_mono refs values refs2 (by simpa [bvOk] using ok) subset
  | _ => simp [bvOk]
termination_by sizeOf value

/-- Domain monotonicity lifted to a list of values. -/
theorem bvOkList_domain_mono (refs : HolFiniteMapExact Nat (Ref Value)) (values : List Value)
    (refs2 : HolFiniteMapExact Nat (Ref Value))
    (ok : bvOkList refs values)
    (subset : ∀ key, refs.lookup key ≠ none → refs2.lookup key ≠ none) :
    bvOkList refs2 values := by
  cases values with
  | nil => simp [bvOkList]
  | cons value values =>
    simp only [bvOkList] at ok ⊢
    exact ⟨bvOk_domain_mono refs value refs2 ok.1 subset,
      bvOkList_domain_mono refs values refs2 ok.2 subset⟩
termination_by sizeOf values
end

/-- Encoding a list of well-formed values yields a well-formed list value. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "list_to_v_ok"
  (fmap_as_finite_support_parameters := [refs])]
theorem listToValue_ok (refs : HolFiniteMapExact Nat (Ref Value)) (values : List Value)
    (ok : ∀ value ∈ values, bvOk refs value) : bvOk refs (listToValue values) := by
  have listOk := (bvOkList_iff refs values).2 ok
  clear ok
  induction values with
  | nil => simp [listToValue, bvOk, bvOkList]
  | cons value values ih =>
    simp only [bvOkList] at listOk
    simp [listToValue, bvOk, bvOkList, listOk.1, ih listOk.2]

/-- Well-formedness of an encoded list exactly reflects its elements. -/
theorem bvOk_listToValue (refs : HolFiniteMapExact Nat (Ref Value)) (values : List Value) :
    bvOk refs (listToValue values) ↔ bvOkList refs values := by
  induction values with
  | nil => simp [listToValue, bvOk, bvOkList]
  | cons value values ih => simp [listToValue, bvOk, bvOkList, ih]

/-- Concatenating two well-formed encoded lists preserves well-formedness. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "list_to_v_ok_APPEND"
  (fmap_as_finite_support_parameters := [refs])]
theorem listToValue_ok_append (refs : HolFiniteMapExact Nat (Ref Value)) (xs ys : List Value)
    (first : bvOk refs (listToValue xs)) (second : bvOk refs (listToValue ys)) :
    bvOk refs (listToValue (xs ++ ys)) := by
  apply listToValue_ok
  have xok := (bvOkList_iff refs xs).1 ((bvOk_listToValue refs xs).1 first)
  have yok := (bvOkList_iff refs ys).1 ((bvOk_listToValue refs ys).1 second)
  intro value member
  rcases List.mem_append.mp member with inX | inY
  · exact xok value inX
  · exact yok value inY

/-- Evaluation preserves well-formedness of values that were already valid
in the input reference domain. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "evaluate_IMP_bv_ok"
  (fmap_as_finite_support := [refs])]
theorem evaluateImpBvOk {C F : Type} (expressions : List Bvl.Exp) (env : List Value)
    (source target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (value : Value) (values : List Value)
    (run : BvlSem.evaluateTuple (expressions, env, source) = (result, target)) :
    (bvOk source.refs value → bvOk target.refs value) ∧
      (bvOkList source.refs values → bvOkList target.refs values) := by
  have subset := BvlProps.evaluateRefsSubset expressions env source target result run
  exact ⟨fun ok => bvOk_domain_mono source.refs value target.refs ok subset,
    fun ok => bvOkList_domain_mono source.refs values target.refs ok subset⟩

/-- Arguments selected by a successful code lookup remain well formed in an
arbitrary reference domain when all supplied arguments are well formed. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "find_code_bv_ok"
  (fmap_as_finite_support_parameters := [refs])]
theorem findCode_bvOk {α : Type} (dest : Option Nat) (values args : List Value)
    (code : Spt (Nat × α)) (body : α)
    (refs : HolFiniteMapExact Nat (Ref Value))
    (run : BvlSem.findCode dest values code = some (args, body))
    (ok : bvOkList refs values) : bvOkList refs args := by
  apply (bvOkList_iff refs args).2
  intro value member
  exact (bvOkList_iff refs values).1 ok value
    (BvlProps.findCode_args_subset dest values args code body run value member)

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
