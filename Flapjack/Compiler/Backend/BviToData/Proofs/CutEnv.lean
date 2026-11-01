import Flapjack.Compiler.Backend.BviToData.Proofs.Variables
import Flapjack.Compiler.Backend.BviToData.Assign
import Flapjack.Compiler.Backend.Semantics.DataSem.Control

/-! Live-name environment cuts used by BVI-to-data assignments. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- The source live-name tree contains exactly the names in the list. -/
theorem namesOfList_mem (names : List Nat) (key : Nat) :
    sptMem key (namesOfList names) ↔ key ∈ names := by
  induction names with
  | nil => simp [namesOfList, sptMem, sptDomain]
  | cons name names ih => simp [namesOfList, sptMem_sptInsert, ih]

/-- A live-name cut succeeds when all requested locals exist. -/
theorem cutEnv_namesOfList {α : Type} (names : List Nat) (env : Spt α)
    (present : ∀ key ∈ names, sptLookup key env ≠ none) :
    DataSem.cutEnv (namesOfList names) env = some (sptMkWf (sptInter env (namesOfList names))) := by
  classical
  unfold DataSem.cutEnv
  apply if_pos
  intro key member
  have existsValue : ∃ value, sptLookup key env = some value := by
    cases found : sptLookup key env with
    | none => exact False.elim (present key ((namesOfList_mem names key).1 member) found)
    | some value => exact ⟨value, rfl⟩
  exact (sptMem_iff_lookup key env).2 existsValue

/-- The cut retains exactly the requested locals, preserving their values. -/
theorem lookup_cut_namesOfList {α : Type} (names : List Nat) (env : Spt α) (key : Nat) :
    sptLookup key (sptMkWf (sptInter env (namesOfList names))) =
      if key ∈ names then sptLookup key env else none := by
  classical
  rw [sptLookup_mkWf, sptLookup_sptInterCases]
  by_cases member : key ∈ names
  · have present := (sptMem_iff_lookup key (namesOfList names)).1 ((namesOfList_mem names key).2 member)
    obtain ⟨marker, found⟩ := present
    cases sptLookup key env <;> simp [member, found]
  · have absent : sptLookup key (namesOfList names) = none := by
      cases found : sptLookup key (namesOfList names) with
      | none => rfl
      | some marker =>
        have contradiction := (namesOfList_mem names key).1 ((sptMem_iff_lookup key _).2 ⟨marker, found⟩)
        exact False.elim (member contradiction)
    simp [member, absent]

/-- A projected variable correspondence survives a cut that keeps all of
its names. The projection can have an independent result type. -/
theorem varCorr_cut_namesOfList {α β : Type} (f : α → β) (kept : List Nat) (env : Spt α)
    (names : List Nat) (values : List β)
    (related : DataProps.varCorr values names (sptMap f env))
    (included : ∀ key ∈ names, key ∈ kept) :
    DataProps.varCorr values names (sptMap f (sptMkWf (sptInter env (namesOfList kept)))) := by
  induction related with
  | nil => constructor
  | @cons name value names values lookup rest ih =>
    constructor
    · simp only [DataSem.getVar, sptLookup_sptMap, lookup_cut_namesOfList]
      rw [if_pos (included name (by simp))]
      simpa [DataSem.getVar, sptLookup_sptMap] using lookup
    · exact ih (fun key member => included key (by simp [member]))

/-- If the variable correspondence's names are live, a cut preserves the
entire corresponding read, in the original order. -/
theorem getVars_cut_namesOfList {α β : Type} (f : α → β) (kept : List Nat) (env : Spt α)
    (names : List Nat) (values : List β)
    (related : DataProps.varCorr values names (sptMap f env))
    (included : ∀ key ∈ names, key ∈ kept) :
    DataSem.getVars names (sptMap f (sptMkWf (sptInter env (namesOfList kept)))) = some values :=
  DataProps.getVars_thm names values _ (varCorr_cut_namesOfList f kept env names values related included)

end Flapjack.Compiler.Backend.BviToData
