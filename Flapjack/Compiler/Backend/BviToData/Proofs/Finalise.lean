module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
public import Flapjack.Compiler.Backend.Semantics.DataSem.Finalise
public import Flapjack.Compiler.Backend.Semantics.BviSem.Finalise
public import Flapjack.Misc.SptreeLookup

@[expose] public section

/-! Finalization simulation across timestamped data values. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- Removing the same reference preserves the lookup projection. -/
private theorem delete_related (dataRefs : Spt (BvlSem.Ref DataSem.Value))
    (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat)
    (related : ∀ n, bviRefs.lookup n = (sptLookup n dataRefs).map dataToBviRef) :
    ∀ n, (bviRefs.eraseEq key).lookup n = (sptLookup n (sptDelete key dataRefs)).map dataToBviRef := by
  intro n
  rw [HolFiniteMapExact.lookup_eraseEq, sptLookup_sptDelete]
  by_cases same : n = key
  · simp [FDOMSUB_HOL, same]
  · simp [FDOMSUB_HOL, same, related]

/-- Reinserting corresponding finalized references preserves lookup projection. -/
private theorem insert_related (dataRefs : Spt (BvlSem.Ref DataSem.Value))
    (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) (value : BvlSem.Ref DataSem.Value)
    (related : ∀ n, bviRefs.lookup n = (sptLookup n dataRefs).map dataToBviRef) :
    ∀ n, (bviRefs.updateEq (key, dataToBviRef value)).lookup n =
      (sptLookup n (sptInsert key value dataRefs)).map dataToBviRef := by
  intro n
  rw [HolFiniteMapExact.lookup_updateEq]
  by_cases same : n = key
  · subst n
    simp [FUPDATE_HOL, sptLookup_sptInsert_same]
  · rw [sptLookup_sptInsert_ne key n value dataRefs same]
    simp [FUPDATE_HOL, same, related]

/-- Successful BVI mutable-constructor finalization has a data counterpart
whose value and reference store project to the BVI result. The timestamp is
threaded through the data side. This proof-side theorem remains untagged
pending review of its finite-map carrier against the HOL statement. -/
theorem finaliseCons_projection (value : DataSem.Value) (refs : Spt (BvlSem.Ref DataSem.Value))
    (timestamp : Option Nat) (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (bviValue : BvlSem.Value) (bviNext : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (related : ∀ n, bviRefs.lookup n = (sptLookup n refs).map dataToBviRef)
    (run : BviSem.finaliseCons (dataToBviValue value) bviRefs = some (bviValue, bviNext)) :
    ∃ dataValue dataNext nextTimestamp, DataSem.finaliseCons value refs timestamp = some (dataValue, dataNext, nextTimestamp) ∧
      bviValue = dataToBviValue dataValue ∧
      ∀ n, bviNext.lookup n = (sptLookup n dataNext).map dataToBviRef := by
  have all : ∀ size : Nat, ∀ (value : DataSem.Value) (refs : Spt (BvlSem.Ref DataSem.Value))
      (timestamp : Option Nat) (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
      (bviValue : BvlSem.Value) (bviNext : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)),
      sptSize refs = size →
      (∀ n, bviRefs.lookup n = (sptLookup n refs).map dataToBviRef) →
      BviSem.finaliseCons (dataToBviValue value) bviRefs = some (bviValue, bviNext) →
      ∃ dataValue dataNext nextTimestamp, DataSem.finaliseCons value refs timestamp = some (dataValue, dataNext, nextTimestamp) ∧
        bviValue = dataToBviValue dataValue ∧ ∀ n, bviNext.lookup n = (sptLookup n dataNext).map dataToBviRef := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
      intro value refs timestamp bviRefs bviValue bviNext sizeEq related run
      cases value with
      | number n =>
        simp [dataToBviValue, BviSem.finaliseCons.eq_def] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨.number n, refs, timestamp, by simp [DataSem.finaliseCons.eq_def], by simp [dataToBviValue], related⟩
      | word64 w =>
        simp [dataToBviValue, BviSem.finaliseCons.eq_def] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨.word64 w, refs, timestamp, by simp [DataSem.finaliseCons.eq_def], by simp [dataToBviValue], related⟩
      | block ts tag values =>
        simp [dataToBviValue, BviSem.finaliseCons.eq_def] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨.block ts tag values, refs, timestamp, by simp [DataSem.finaliseCons.eq_def], by simp [dataToBviValue], related⟩
      | codePtr label =>
        simp [dataToBviValue, BviSem.finaliseCons.eq_def] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨.codePtr label, refs, timestamp, by simp [DataSem.finaliseCons.eq_def], by simp [dataToBviValue], related⟩
      | refPtr bit ptr =>
        simp only [dataToBviValue] at run
        rw [BviSem.finaliseCons.eq_def] at run
        dsimp only at run
        cases found : sptLookup ptr refs with
        | none =>
          have empty : bviRefs.lookup ptr = none := by simp [related ptr, found]
          rw [empty] at run
          cases run
        | some entry =>
          have lookup : bviRefs.lookup ptr = some (dataToBviRef entry) := by simp [related ptr, found]
          rw [lookup] at run
          cases entry with
          | valueArray values =>
            simp [dataToBviRef] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.refPtr bit ptr, refs, timestamp, by rw [DataSem.finaliseCons.eq_def]; dsimp only; rw [found], by simp [dataToBviValue], related⟩
          | byteArray flag bytes =>
            simp [dataToBviRef] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.refPtr bit ptr, refs, timestamp, by rw [DataSem.finaliseCons.eq_def]; dsimp only; rw [found], by simp [dataToBviValue], related⟩
          | thunk mode body =>
            simp [dataToBviRef] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.refPtr bit ptr, refs, timestamp, by rw [DataSem.finaliseCons.eq_def]; dsimp only; rw [found], by simp [dataToBviValue], related⟩
          | mutBlock tag finalised left child right =>
            cases finalised with
            | true => simp [dataToBviRef] at run
            | false =>
              simp only [dataToBviRef, Bool.false_eq_true,
                ↓reduceIte] at run
              cases recursive : BviSem.finaliseCons (dataToBviValue child) (bviRefs.eraseEq ptr) with
              | none => simp [recursive] at run
              | some pair =>
                obtain ⟨result, nextRefs⟩ := pair
                simp only [recursive, Option.some.injEq, Prod.mk.injEq] at run
                obtain ⟨rfl, rfl⟩ := run
                have smaller : sptSize (sptDelete ptr refs) < size := by
                  rw [← sizeEq]
                  exact sptSize_delete_lt refs ptr (by simp [found])
                obtain ⟨dataValue, dataNext, nextTimestamp, dataRun, valueEq, nextRel⟩ :=
                  ih _ smaller child (sptDelete ptr refs) timestamp (bviRefs.eraseEq ptr) result nextRefs rfl
                    (delete_related refs bviRefs ptr related) recursive
                refine ⟨.block (nextTimestamp.getD 0) tag (left ++ [dataValue] ++ right),
                  sptInsert ptr (.mutBlock tag true left child right) dataNext, nextTimestamp.map (· + 1), ?_, ?_, ?_⟩
                · rw [DataSem.finaliseCons.eq_def]
                  dsimp only
                  rw [found]
                  simp only [Bool.false_eq_true, ↓reduceIte, dataRun]
                · simp [dataToBviValue, List.map_append, valueEq]
                · simpa [dataToBviRef] using
                    insert_related dataNext nextRefs ptr (.mutBlock tag true left child right) nextRel
  exact all (sptSize refs) value refs timestamp bviRefs bviValue bviNext rfl related run

end Flapjack.Compiler.Backend.BviToData
