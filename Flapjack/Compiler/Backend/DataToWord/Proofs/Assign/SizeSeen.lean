import Flapjack.Compiler.Backend.Semantics.DataSem.Heap.SizeProperties
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.SizeValues

/-! Seen-timestamp monotonicity for the data-to-word assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend

/-- Source sizing preserves the domain of the input seen-timestamp tree. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "size_of_seen_SUBSET"]
theorem sizeOfValues_seen_subset (limits : DataSem.Limits) (values : List DataSem.Value)
    (refs refs1 : Spt (BvlSem.Ref DataSem.Value)) (seen seen1 : Spt Unit) (n : Nat)
    (run : DataSem.sizeOfValues limits values refs seen = (n, refs1, seen1)) :
    ({key | sptDomain seen key} : Set Nat) ⊆ {key | sptDomain seen1 key} := by
  have subset := DataSem.sizeOfValues_seenSubspt limits values refs seen
  rw [run] at subset
  exact fun key member => (subset key member).1

/-- Flapjack infrastructure: sizing a nonempty block records its timestamp. -/
theorem sizeOfValues_singleBlock_seen (limits : DataSem.Limits) (stamp tag : Nat)
    (head : DataSem.Value) (tail : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) :
    sptLookup stamp (DataSem.sizeOfValues limits [.block stamp tag (head :: tail)] refs seen).2.2 = some () := by
  by_cases present : (sptLookup stamp seen).isSome = true
  · cases found : sptLookup stamp seen with
    | none => simp [found] at present
    | some value => cases value; simpa [DataSem.sizeOfValues, present] using found
  · have inInserted : sptLookup stamp (sptInsert stamp () seen) = some () :=
      sptLookup_sptInsert_same stamp () seen
    have preserve := DataSem.sizeOfValues_seenSubspt limits (head :: tail) refs (sptInsert stamp () seen)
    have result := (sptSubsptLookup _ _).mp preserve stamp () inInserted
    cases sized : DataSem.sizeOfValues limits (head :: tail) refs (sptInsert stamp () seen) with
    | mk n rest =>
      cases rest
      rw [sized] at result
      simpa [DataSem.sizeOfValues, present, sized] using result

/-- Every nonempty block among the sized roots has its timestamp recorded in
the final seen tree. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "size_of_seen_Block"]
theorem sizeOfValues_seen_block (limits : DataSem.Limits) (values : List DataSem.Value)
    (refs refs1 : Spt (BvlSem.Ref DataSem.Value)) (seen seen1 : Spt Unit) (n stamp tag : Nat)
    (fields : List DataSem.Value)
    (run : DataSem.sizeOfValues limits values refs seen = (n, refs1, seen1))
    (member : .block stamp tag fields ∈ values) (nonempty : fields ≠ []) :
    sptLookup stamp seen1 = some () := by
  induction values generalizing refs refs1 seen seen1 n with
  | nil => simp at member
  | cons head tail ih =>
    rw [Gc.sizeOfValues_cons] at run
    cases first : DataSem.sizeOfValues limits tail refs seen with
    | mk n1 rest =>
      obtain ⟨refsMid, seenMid⟩ := rest
      cases second : DataSem.sizeOfValues limits [head] refsMid seenMid with
      | mk n2 rest2 =>
        obtain ⟨refsEnd, seenEnd⟩ := rest2
        simp only [first, second, Prod.mk.injEq] at run
        obtain ⟨_, _, rfl⟩ := run
        simp only [List.mem_cons] at member
        rcases member with same | later
        · subst head
          cases fields with
          | nil => exact False.elim (nonempty rfl)
          | cons x xs =>
            have result := sizeOfValues_singleBlock_seen limits stamp tag x xs refsMid seenMid
            simpa [second] using result
        · have mid := ih refs refsMid seen seenMid n1 first later
          have preserve := DataSem.sizeOfValues_seenSubspt limits [head] refsMid seenMid
          rw [second] at preserve
          exact (sptSubsptLookup _ _).mp preserve stamp () mid

/-- A block already present in the remaining roots adds no second sizing
charge when prepended. The exported HOL theorem's inferred type has not yet
been captured for source review. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "size_of_cons_seen_Block"]
theorem sizeOfValues_cons_seen_block (limits : DataSem.Limits) (values : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) (stamp tag : Nat)
    (fields : List DataSem.Value) (member : .block stamp tag fields ∈ values) :
    DataSem.sizeOfValues limits (.block stamp tag fields :: values) refs seen =
      DataSem.sizeOfValues limits values refs seen := by
  rw [Gc.sizeOfValues_cons]
  cases first : DataSem.sizeOfValues limits values refs seen with
  | mk n rest =>
    obtain ⟨refs1, seen1⟩ := rest
    cases fields with
    | nil => simp [DataSem.sizeOfValues]
    | cons head tail =>
      have found := sizeOfValues_seen_block limits values refs refs1 seen seen1 n stamp tag (head :: tail)
        first member (by simp)
      simp [Gc.sizeOfValues_block, found]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
