module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
public import Flapjack.Compiler.Backend.Semantics.DataSem.Equality
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Equality
public import Flapjack.Misc.Sptree.Map
public import Flapjack.FiniteMap.CardinalityExact
public import Mathlib.Tactic.CasesM

@[expose] public section

/-! Equality under the BVI-to-data value projection. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

mutual
/-- Flapjack proof infrastructure: equality agrees under timestamp erasure
when the reference lookups agree. -/
theorem doEqProjection (dataRefs : Spt (BvlSem.Ref DataSem.Value))
    (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (related : ∀ n, bviRefs.lookup n = sptLookup n (sptMap dataToBviRef dataRefs))
    (first second : DataSem.Value) :
    BvlSem.doEq bviRefs (dataToBviValue first) (dataToBviValue second) =
      DataSem.doEq dataRefs first second := by
  cases first with
  | number n => cases second <;> simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
  | word64 w => cases second <;> simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
  | codePtr p => cases second <;> simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
  | refPtr bit addr =>
    cases second with
    | number n => simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
    | word64 w => simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
    | codePtr p => simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
    | block t tag vs => simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
    | refPtr bit2 addr2 =>
      cases bit <;> cases bit2 <;>
        simp [dataToBviValue, BvlSem.doEq, DataSem.doEq, related, sptLookup_sptMap]
      generalize sptLookup addr dataRefs = left
      generalize sptLookup addr2 dataRefs = right
      cases left with
      | none =>
        cases right with
        | none => rfl
        | some r =>
          cases r
          all_goals try (cases_type Bool)
          all_goals rfl
      | some l =>
        cases right with
        | none =>
          cases l
          all_goals try (cases_type Bool)
          all_goals rfl
        | some r =>
          cases l <;> cases r
          all_goals try (cases_type Bool)
          all_goals try (cases_type Bool)
          all_goals rfl
  | block time tag values =>
    cases second with
    | number n => simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
    | word64 w => simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
    | codePtr p => simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
    | refPtr bit addr => simp [dataToBviValue, BvlSem.doEq, DataSem.doEq]
    | block time2 tag2 values2 =>
      have clos (tag : Nat) (xs : List DataSem.Value) :
          BvlSem.isClosure tag (xs.map dataToBviValue) ↔ DataSem.isClosure tag xs := by
        simp [BvlSem.isClosure, DataSem.isClosure]
      simp only [dataToBviValue, BvlSem.doEq, DataSem.doEq, List.length_map, clos]
      split
      · split <;> rfl
      · split
        · exact doEqListProjection dataRefs bviRefs related values values2
        · rfl
termination_by sizeOf first

/-- Flapjack proof infrastructure: corresponding left-to-right list
comparisons also agree. -/
theorem doEqListProjection (dataRefs : Spt (BvlSem.Ref DataSem.Value))
    (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (related : ∀ n, bviRefs.lookup n = sptLookup n (sptMap dataToBviRef dataRefs))
    (first second : List DataSem.Value) :
    BvlSem.doEqList bviRefs (first.map dataToBviValue) (second.map dataToBviValue) =
      DataSem.doEqList dataRefs first second := by
  cases first with
  | nil => cases second <;> simp [BvlSem.doEqList, DataSem.doEqList]
  | cons head tail =>
    cases second with
    | nil => simp [BvlSem.doEqList, DataSem.doEqList]
    | cons head2 tail2 =>
      simp only [List.map_cons, BvlSem.doEqList, DataSem.doEqList]
      rw [doEqProjection dataRefs bviRefs related head head2]
      cases h : DataSem.doEq dataRefs head head2 with
      | typeError => rfl
      | val b =>
        cases b with
        | false => rfl
        | true => exact doEqListProjection dataRefs bviRefs related tail tail2
termination_by sizeOf first
end

/-- The first universally quantified reference map survives its codec. -/
theorem holFmapAsFiniteSupportParamWitness_dataToBviDoEq_r1
    (r1 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality r1) r1.finiteSupport).lookup key = r1.lookup key ∧
    (HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality r1) r1.finiteSupport).finiteSupport = r1.finiteSupport ∧
    HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality r1) r1.finiteSupport = r1 := by
  cases r1
  exact ⟨rfl, rfl, rfl⟩

/-- The second universally quantified reference map survives its codec. -/
theorem holFmapAsFiniteSupportParamWitness_dataToBviDoEq_r2
    (r2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality r2) r2.finiteSupport).lookup key = r2.lookup key ∧
    (HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality r2) r2.finiteSupport).finiteSupport = r2.finiteSupport ∧
    HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality r2) r2.finiteSupport = r2 := by
  cases r2
  exact ⟨rfl, rfl, rfl⟩

/-- The two equality simulations, assembled in the quantifier order of the
HOL result. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_do_eq"
  (fmap_as_finite_support_parameters := [r1, r2])]
theorem dataToBviDoEq :
    (∀ (t : Spt (BvlSem.Ref DataSem.Value)) v₁ v₂
      (r1 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)),
      (∀ n, r1.lookup n = sptLookup n (sptMap dataToBviRef t)) →
      BvlSem.doEq r1 (dataToBviValue v₁) (dataToBviValue v₂) = DataSem.doEq t v₁ v₂) ∧
    (∀ (t : Spt (BvlSem.Ref DataSem.Value)) l₁ l₂
      (r2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)),
      (∀ n, r2.lookup n = sptLookup n (sptMap dataToBviRef t)) →
      BvlSem.doEqList r2 (l₁.map dataToBviValue) (l₂.map dataToBviValue) =
        DataSem.doEqList t l₁ l₂) :=
  ⟨fun t v₁ v₂ r h => doEqProjection t r h v₁ v₂,
   fun t l₁ l₂ r h => doEqListProjection t r h l₁ l₂⟩

end
end Flapjack.Compiler.Backend.BviToData
