module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
public import Flapjack.Compiler.Backend.Semantics.DataSem.Build
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Build

@[expose] public section

/-! Timestamped list and constant construction under value projection. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.Compiler.Backend.BackendCommon

/-- A constructed nil-terminated data list projects to the corresponding
BVI list, independent of the initial timestamp. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_v_list_to_v_Nil"]
theorem dataToBviValue_listToValue_nil (values : List DataSem.Value) (timestamp : Nat) :
    dataToBviValue (DataSem.listToValue timestamp (.block 0 nilTag []) values) =
      BvlSem.listToValue (values.map dataToBviValue) := by
  induction values generalizing timestamp with
  | nil => simp [DataSem.listToValue, BvlSem.listToValue, dataToBviValue]
  | cons first rest ih => simp [DataSem.listToValue, BvlSem.listToValue, dataToBviValue, ih]

/-- Changing the timestamps assigned to new list blocks leaves their BVI
projection unchanged. This is Flapjack proof infrastructure. -/
theorem dataToBviValue_listToValue_timestamp (values : List DataSem.Value) (tail : DataSem.Value)
    (left right : Nat) :
    dataToBviValue (DataSem.listToValue left tail values) = dataToBviValue (DataSem.listToValue right tail values) := by
  induction values generalizing left right with
  | nil => rfl
  | cons first rest ih =>
    simp only [DataSem.listToValue, dataToBviValue, List.map_cons, List.map_nil]
    rw [ih (left + 1) (right + 1)]

private theorem bvlList_reconstruct (value : BvlSem.Value) (values : List BvlSem.Value)
    (decode : BvlSem.valueToList value = some values) : BvlSem.listToValue values = value := by
  cases value with
  | block tag fields =>
    cases fields with
    | nil =>
      simp only [BvlSem.valueToList] at decode
      split at decode
      · rename_i equal
        simp only [Option.some.injEq] at decode
        subst values
        subst tag
        rfl
      · contradiction
    | cons head tail =>
      cases tail with
      | nil => simp [BvlSem.valueToList] at decode
      | cons next rest =>
        cases rest with
        | cons other rest => simp [BvlSem.valueToList] at decode
        | nil =>
          simp only [BvlSem.valueToList] at decode
          split at decode
          · rename_i equal
            cases nextDecode : BvlSem.valueToList next with
            | none => simp [nextDecode] at decode
            | some vs =>
              simp [nextDecode] at decode
              subst values
              have ih := bvlList_reconstruct next vs nextDecode
              subst tag
              simp [BvlSem.listToValue, ih]
          · contradiction
  | _ => simp [BvlSem.valueToList] at decode
termination_by sizeOf value

/-- Constructing a list onto a valid list tail agrees, after timestamp erasure,
with constructing the concatenation onto nil. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_v_list_to_v_APPEND"]
theorem dataToBviValue_listToValue_append (front suffix : List DataSem.Value)
    (tail : DataSem.Value) (timestamp : Nat) (decoded : DataSem.valueToList tail = some suffix) :
    dataToBviValue (DataSem.listToValue timestamp tail front) =
      dataToBviValue (DataSem.listToValue timestamp (.block 0 nilTag []) (front ++ suffix)) := by
  have projectedDecode : BvlSem.valueToList (dataToBviValue tail) = some (suffix.map dataToBviValue) := by
    rw [← dataToBviValue_valueToList, decoded]
    rfl
  have tailEq := (bvlList_reconstruct (dataToBviValue tail) (suffix.map dataToBviValue) projectedDecode).symm
  induction front generalizing timestamp with
  | nil => simpa only [List.nil_append, DataSem.listToValue, dataToBviValue_listToValue_nil] using tailEq
  | cons first rest ih =>
    simp only [List.cons_append, DataSem.listToValue, dataToBviValue, List.map_cons, List.map_nil]
    rw [ih (timestamp + 1)]

/-- Lookup-related reference stores choose the same least free index. -/
theorem leastUnusedRef_projection (dataRefs : Spt (BvlSem.Ref DataSem.Value))
    (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (related : ∀ key, bviRefs.lookup key = (sptLookup key dataRefs).map dataToBviRef) :
    BvlSem.leastUnusedRef bviRefs = DataSem.leastUnusedRef dataRefs := by
  apply BvlSem.leastUnusedRef_eq bviRefs (DataSem.leastUnusedRef dataRefs)
  · rw [related, DataSem.leastUnusedRef_unused]
    rfl
  · intro index smaller
    have occupied := DataSem.leastUnusedRef_minimal dataRefs index smaller
    rw [related]
    cases h : sptLookup index dataRefs with
    | none => exact False.elim (occupied h)
    | some value => simp

/-- One timestamped constant part and its BVI counterpart produce related
values and reference stores. This is Flapjack pass-simulation infrastructure. -/
theorem doPart_projection (dataValues : Nat → DataSem.Value) (bviValues : Nat → BvlSem.Value)
    (part : ClosLang.ConstPart) (dataRefs : Spt (BvlSem.Ref DataSem.Value))
    (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (timestamp : Option Nat)
    (valuesRel : ∀ index, bviValues index = dataToBviValue (dataValues index))
    (refsRel : ∀ key, bviRefs.lookup key = (sptLookup key dataRefs).map dataToBviRef) :
    (BvlSem.doPart bviValues part bviRefs).1 = dataToBviValue (DataSem.doPart dataValues part dataRefs timestamp).1 ∧
    ∀ key, (BvlSem.doPart bviValues part bviRefs).2.lookup key =
      (sptLookup key (DataSem.doPart dataValues part dataRefs timestamp).2.1).map dataToBviRef := by
  cases part with
  | int i => simp [DataSem.doPart, BvlSem.doPart, dataToBviValue, refsRel]
  | w64 word => simp [DataSem.doPart, BvlSem.doPart, dataToBviValue, refsRel]
  | con tag indices =>
    cases indices with
    | nil => simp [DataSem.doPart, BvlSem.doPart, dataToBviValue, refsRel]
    | cons first rest =>
      cases timestamp <;> simp [DataSem.doPart, BvlSem.doPart, dataToBviValue, refsRel, valuesRel, List.map_map]
  | str value =>
    have indexEq := leastUnusedRef_projection dataRefs bviRefs refsRel
    constructor
    · simp [DataSem.doPart, BvlSem.doPart, dataToBviValue, indexEq]
    · intro key
      simp only [DataSem.doPart, BvlSem.doPart, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, indexEq]
      by_cases same : key = DataSem.leastUnusedRef dataRefs
      · subst key
        simp [sptLookup_sptInsert_same, dataToBviRef]
      · rw [sptLookup_sptInsert_ne (DataSem.leastUnusedRef dataRefs) key _ _ same]
        simp [same, refsRel]

/-- Sequential constant construction preserves value projection and the
lookup relation between the resulting reference stores. -/
theorem doBuild_projection (parts : List ClosLang.ConstPart) (dataValues : Nat → DataSem.Value)
    (bviValues : Nat → BvlSem.Value) (index : Nat) (dataRefs : Spt (BvlSem.Ref DataSem.Value))
    (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (timestamp : Option Nat)
    (valuesRel : ∀ key, bviValues key = dataToBviValue (dataValues key))
    (refsRel : ∀ key, bviRefs.lookup key = (sptLookup key dataRefs).map dataToBviRef) :
    (BvlSem.doBuild bviValues index parts bviRefs).1 = dataToBviValue (DataSem.doBuild dataValues index parts dataRefs timestamp).1 ∧
    ∀ key, (BvlSem.doBuild bviValues index parts bviRefs).2.lookup key =
      (sptLookup key (DataSem.doBuild dataValues index parts dataRefs timestamp).2.1).map dataToBviRef := by
  induction parts generalizing dataValues bviValues index dataRefs bviRefs timestamp with
  | nil => simp [DataSem.doBuild, BvlSem.doBuild, valuesRel, refsRel]
  | cons first rest ih =>
    have one := doPart_projection dataValues bviValues first dataRefs bviRefs timestamp valuesRel refsRel
    cases dataRun : DataSem.doPart dataValues first dataRefs timestamp with
    | mk dataValue dataTail =>
      obtain ⟨nextDataRefs, nextTimestamp⟩ := dataTail
      cases bviRun : BvlSem.doPart bviValues first bviRefs with
      | mk bviValue nextBviRefs =>
        simp only [dataRun, bviRun] at one
        simp only [DataSem.doBuild, BvlSem.doBuild, dataRun, bviRun]
        apply ih _ _ (index + 1) nextDataRefs nextBviRefs nextTimestamp ?_ one.2
        intro key
        by_cases same : key = index
        · simp [same, one.1]
        · simp [same, valuesRel]

/-- The source's zero-initialized constant builders agree after projection. -/
theorem doBuildConst_projection (parts : List ClosLang.ConstPart)
    (dataRefs : Spt (BvlSem.Ref DataSem.Value)) (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (timestamp : Option Nat)
    (refsRel : ∀ key, bviRefs.lookup key = (sptLookup key dataRefs).map dataToBviRef) :
    (BvlSem.doBuildConst parts bviRefs).1 = dataToBviValue (DataSem.doBuildConst parts dataRefs timestamp).1 ∧
    ∀ key, (BvlSem.doBuildConst parts bviRefs).2.lookup key =
      (sptLookup key (DataSem.doBuildConst parts dataRefs timestamp).2.1).map dataToBviRef := by
  exact doBuild_projection parts (fun _ => .number 0) (fun _ => .number 0) 0 dataRefs bviRefs timestamp
    (by intro key; simp [dataToBviValue]) refsRel

end Flapjack.Compiler.Backend.BviToData
