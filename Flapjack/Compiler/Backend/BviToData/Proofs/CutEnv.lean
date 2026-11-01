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

/-- A successful optional compiler root cut preserves every listed local. -/
theorem cutStateOpt_names_keep {C F : Type} (enabled : Bool) (roots : List Nat)
    (state prepared : DataSem.State C F) (key : Nat) (member : key ∈ roots)
    (run : DataSem.cutStateOpt (if enabled then some (namesOfList roots) else none) state = some prepared) :
    sptLookup key prepared.locals = sptLookup key state.locals := by
  cases enabled with
  | false =>
    simp [DataSem.cutStateOpt] at run
    subst prepared
    rfl
  | true =>
    cases cut : DataSem.cutEnv (namesOfList roots) state.locals with
    | none => simp [DataSem.cutStateOpt, DataSem.cutState, cut] at run
    | some env =>
      simp [DataSem.cutStateOpt, DataSem.cutState, cut] at run
      subst prepared
      unfold DataSem.cutEnv at cut
      split at cut
      · simp only [Option.some.injEq] at cut
        subst env
        simp [lookup_cut_namesOfList, member]
      · simp at cut

/-- The optional root cut either preserves each local or removes it when the
cut is enabled and the name is absent from the root list. -/
theorem cutStateOpt_names_lookup {C F : Type} (enabled : Bool) (roots : List Nat)
    (state prepared : DataSem.State C F) (key : Nat)
    (run : DataSem.cutStateOpt (if enabled then some (namesOfList roots) else none) state = some prepared) :
    sptLookup key prepared.locals =
      if enabled then (if key ∈ roots then sptLookup key state.locals else none) else sptLookup key state.locals := by
  classical
  cases enabled with
  | false =>
    simp [DataSem.cutStateOpt] at run
    subst prepared
    rfl
  | true =>
    cases cut : DataSem.cutEnv (namesOfList roots) state.locals with
    | none => simp [DataSem.cutStateOpt, DataSem.cutState, cut] at run
    | some env =>
      simp [DataSem.cutStateOpt, DataSem.cutState, cut] at run
      subst prepared
      unfold DataSem.cutEnv at cut
      split at cut
      · simp only [Option.some.injEq] at cut
        subst env
        exact lookup_cut_namesOfList roots state.locals key
      · simp at cut

/-- A successful make-space instruction cuts its locals to precisely the
compiler's named roots. -/
theorem evaluate_makeSpace_names_locals {C F : Type} (amount : Nat) (roots : List Nat)
    (state next : DataSem.State C F)
    (run : DataSem.evaluate (.makeSpace amount (namesOfList roots)) state = (none, next)) :
    next.locals = sptMkWf (sptInter state.locals (namesOfList roots)) := by
  cases cut : DataSem.cutEnv (namesOfList roots) state.locals with
  | none => simp [DataSem.evaluate, cut] at run
  | some env =>
    simp [DataSem.evaluate, cut] at run
    subst next
    unfold DataSem.cutEnv at cut
    split at cut
    · simp only [Option.some.injEq] at cut
      subst env
      rfl
    · simp at cut

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

/-- A projected correspondence is preserved when each of its named lookups
is unchanged. -/
theorem varCorr_of_lookup_eq {α β : Type} (f : α → β) (before after : Spt α)
    (names : List Nat) (values : List β) (related : DataProps.varCorr values names (sptMap f before))
    (same : ∀ key ∈ names, sptLookup key after = sptLookup key before) :
    DataProps.varCorr values names (sptMap f after) := by
  induction related with
  | nil => constructor
  | @cons name value names values lookup rest ih =>
    constructor
    · simp only [DataSem.getVar, sptLookup_sptMap] at lookup ⊢
      rw [same name (by simp)]
      exact lookup
    · exact ih (fun key member => same key (by simp [member]))

/-- If the variable correspondence's names are live, a cut preserves the
entire corresponding read, in the original order. -/
theorem getVars_cut_namesOfList {α β : Type} (f : α → β) (kept : List Nat) (env : Spt α)
    (names : List Nat) (values : List β)
    (related : DataProps.varCorr values names (sptMap f env))
    (included : ∀ key ∈ names, key ∈ kept) :
    DataSem.getVars names (sptMap f (sptMkWf (sptInter env (namesOfList kept)))) = some values :=
  DataProps.getVars_thm names values _ (varCorr_cut_namesOfList f kept env names values related included)

/-- A successful unprojected read is unchanged when the cut retains every
requested name. -/
theorem getVars_cut_exact {α : Type} (kept : List Nat) (env : Spt α)
    (names : List Nat) (values : List α)
    (read : DataSem.getVars names env = some values)
    (included : ∀ key ∈ names, key ∈ kept) :
    DataSem.getVars names (sptMkWf (sptInter env (namesOfList kept))) = some values := by
  induction names generalizing values with
  | nil => simpa [DataSem.getVars] using read
  | cons name names ih =>
    have member : name ∈ kept := included name (by simp)
    simp only [DataSem.getVars, DataSem.getVar, lookup_cut_namesOfList, if_pos member] at read ⊢
    cases found : sptLookup name env with
    | none => simp [found] at read
    | some value =>
      simp only [found] at read ⊢
      cases rest : DataSem.getVars names env with
      | none => simp [rest] at read
      | some tail =>
        simp [rest] at read
        subst values
        have restRead := ih tail rest (fun key member => included key (by simp [member]))
        simp [restRead]

/-- A successful variable-list read produces one value for each name. -/
theorem getVars_length {α : Type} (names : List Nat) (env : Spt α) (values : List α)
    (read : DataSem.getVars names env = some values) : values.length = names.length := by
  induction names generalizing values with
  | nil => simpa [DataSem.getVars] using read.symm
  | cons name names ih =>
    simp only [DataSem.getVars] at read
    cases found : DataSem.getVar name env with
    | none => simp [found] at read
    | some value =>
      simp only [found] at read
      cases rest : DataSem.getVars names env with
      | none => simp [rest] at read
      | some tail =>
        simp [rest] at read
        subst values
        simp [ih tail rest]

/-- Every name in a successful variable-list read is present in the tree. -/
theorem getVars_present {α : Type} (names : List Nat) (env : Spt α) (values : List α)
    (read : DataSem.getVars names env = some values) :
    ∀ key ∈ names, sptLookup key env ≠ none := by
  induction names generalizing values with
  | nil => simp
  | cons name names ih =>
    simp only [DataSem.getVars] at read
    cases found : DataSem.getVar name env with
    | none => simp [found] at read
    | some value =>
      simp only [found] at read
      cases rest : DataSem.getVars names env with
      | none => simp [rest] at read
      | some tail =>
        intro key member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · simp [DataSem.getVar] at found
          rw [found]
          simp
        · exact ih tail rest key member

end Flapjack.Compiler.Backend.BviToData
