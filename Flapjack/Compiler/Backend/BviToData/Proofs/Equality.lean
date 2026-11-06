import Flapjack.Compiler.Backend.BviToData.Proofs.Value
import Flapjack.Compiler.Backend.Semantics.DataSem.Equality
import Flapjack.Compiler.Backend.Semantics.BvlSem.Equality
import Flapjack.Misc.Sptree.Map
import Mathlib.Tactic.CasesM

/-! Equality under the BVI-to-data value projection. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

mutual
/-- Equality agrees under timestamp erasure when the reference lookups agree.
This factored lemma is untagged; the HOL conjunction and its finite-map
representation still require a port review. -/
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

/-- The corresponding left-to-right list comparisons also agree. This is
factored proof infrastructure for the same unreviewed HOL conjunction. -/
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

/-- The two equality simulations, assembled in the quantifier order of the
HOL result. This remains untagged pending review of its finite-map carrier and
the complete source statement. -/
theorem dataToBviDoEq :
    (∀ (t : Spt (BvlSem.Ref DataSem.Value)) v₁ v₂
      (r : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)),
      (∀ n, r.lookup n = sptLookup n (sptMap dataToBviRef t)) →
      BvlSem.doEq r (dataToBviValue v₁) (dataToBviValue v₂) = DataSem.doEq t v₁ v₂) ∧
    (∀ (t : Spt (BvlSem.Ref DataSem.Value)) l₁ l₂
      (r : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)),
      (∀ n, r.lookup n = sptLookup n (sptMap dataToBviRef t)) →
      BvlSem.doEqList r (l₁.map dataToBviValue) (l₂.map dataToBviValue) =
        DataSem.doEqList t l₁ l₂) :=
  ⟨fun t v₁ v₂ r h => doEqProjection t r h v₁ v₂,
   fun t l₁ l₂ r h => doEqListProjection t r h l₁ l₂⟩

end
end Flapjack.Compiler.Backend.BviToData
