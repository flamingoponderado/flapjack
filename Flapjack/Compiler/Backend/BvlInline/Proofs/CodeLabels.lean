module

public import Flapjack.Compiler.Backend.BvlInline.RemoveTicks
public import Flapjack.Compiler.Backend.BvlInline.LetOp
public import Flapjack.Compiler.Backend.BvlInline.SourceCompile
public import Flapjack.Compiler.Backend.BvlInline.TickInline
public import Flapjack.Compiler.Backend.BvlInline.Program
public import Flapjack.Misc.Sptree.ToList
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.Semantics.BvlProps.CodeLabels

@[expose] public section

/-! Code-label preservation for BVL inlining passes. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlProps

/-- A recognized variable list contains no code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "var_list_code_labels_imp"]
theorem varList_codeLabels {α : Type} (n : Nat) (xs : List Bvl.Exp) (ys : List α)
    (valid : varListHOL n xs ys = true) :
    (⋃₀ (getCodeLabels '' {e | e ∈ xs})) = ∅ := by
  rw [← getCodeLabelsList_eq]
  induction xs generalizing n ys with
  | nil => simp [getCodeLabelsList]
  | cons e es ih =>
    cases ys with
    | nil => cases e <;> simp_all [varListHOL]
    | cons y ys =>
      cases e <;> simp_all [varListHOL, getCodeLabelsList, getCodeLabels]
      exact ih (n + 1) ys valid.2

private theorem destOp_labels {α : Type} (body : Bvl.Exp) (args : List α) (op : ClosLang.Op)
    (found : destOp body args = some op) : getCodeLabels body = ClosLang.assignGetCodeLabel op := by
  cases body with
  | op operation variables =>
    simp only [destOp] at found
    split at found
    · rename_i valid
      cases found
      have empty := varList_codeLabels 0 variables args valid
      rw [← getCodeLabelsList_eq] at empty
      simp only [getCodeLabels, empty, Set.union_empty]
    · simp at found
  | _ => simp [destOp] at found

mutual
private theorem letOpOne_labels (e : Bvl.Exp) : getCodeLabels (letOpOne e) = getCodeLabels e := by
  cases e with
  | var n => simp only [letOpOne]
  | force loc n => simp only [letOpOne]
  | ifThenElse x y z =>
    simp only [letOpOne, getCodeLabels, letOpOne_labels x, letOpOne_labels y, letOpOne_labels z]
  | «let» xs body =>
    have bindings := letOpList_labels xs
    have bodyLabels := letOpOne_labels body
    simp only [letOpOne]
    cases found : destOp (letOpOne body) (letOpList xs) with
    | none => simp only [getCodeLabels, bindings, bodyLabels]
    | some op =>
      have operation := destOp_labels (letOpOne body) (letOpList xs) op found
      simp only [getCodeLabels]
      rw [← operation, bindings, bodyLabels]
      exact Set.union_comm _ _
  | raise x => simpa only [letOpOne, getCodeLabels] using letOpOne_labels x
  | tick x => simpa only [letOpOne, getCodeLabels] using letOpOne_labels x
  | handle x y => simp only [letOpOne, getCodeLabels, letOpOne_labels x, letOpOne_labels y]
  | op op xs => simp only [letOpOne, getCodeLabels, letOpList_labels xs]
  | call ticks dest xs => simp only [letOpOne, getCodeLabels, letOpList_labels xs]
termination_by sizeOf e

private theorem letOpList_labels (xs : List Bvl.Exp) :
    getCodeLabelsList (letOpList xs) = getCodeLabelsList xs := by
  cases xs with
  | nil => simp only [letOpList]
  | cons x xs => simp only [letOpList, getCodeLabelsList, letOpOne_labels x, letOpList_labels xs]
termination_by sizeOf xs
end

/-- The let-operation pass preserves the complete union of input labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "let_op_code_labels"]
theorem letOp_codeLabels (xs : List Bvl.Exp) :
    (⋃₀ (getCodeLabels '' {e | e ∈ letOp xs})) =
      (⋃₀ (getCodeLabels '' {e | e ∈ xs})) := by
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq]
  exact letOpList_labels xs

/-- The singleton let-operation pass preserves code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "let_op_sing_code_labels"]
theorem letOpSing_codeLabels (e : Bvl.Exp) : getCodeLabels (letOpSing e) = getCodeLabels e := by
  simpa [letOpSing, letOp, letOpList] using letOpOne_labels e

mutual
private theorem removeTicksSing_labels (e : Bvl.Exp) :
    getCodeLabels (removeTicksSing e) = getCodeLabels e := by
  cases e with
  | var n => simp only [removeTicksSing]
  | force loc n => simp only [removeTicksSing]
  | ifThenElse x y z =>
    simp only [removeTicksSing, getCodeLabels, removeTicksSing_labels x,
      removeTicksSing_labels y, removeTicksSing_labels z]
  | «let» xs body =>
    simp only [removeTicksSing, getCodeLabels, removeTicksList_labels xs, removeTicksSing_labels body]
  | raise x => simpa only [removeTicksSing, getCodeLabels] using removeTicksSing_labels x
  | tick x => simpa only [removeTicksSing, getCodeLabels] using removeTicksSing_labels x
  | handle x y =>
    simp only [removeTicksSing, getCodeLabels, removeTicksSing_labels x, removeTicksSing_labels y]
  | op op xs => simp only [removeTicksSing, getCodeLabels, removeTicksList_labels xs]
  | call ticks dest xs => simp only [removeTicksSing, getCodeLabels, removeTicksList_labels xs]
termination_by sizeOf e

private theorem removeTicksList_labels (xs : List Bvl.Exp) :
    getCodeLabelsList (removeTicksList xs) = getCodeLabelsList xs := by
  cases xs with
  | nil => simp only [removeTicksList]
  | cons x xs =>
    simp only [removeTicksList, getCodeLabelsList, removeTicksSing_labels x, removeTicksList_labels xs]
termination_by sizeOf xs
end

/-- Removing ticks preserves the complete union of input code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "remove_ticks_code_labels"]
theorem removeTicks_codeLabels (xs : List Bvl.Exp) :
    (⋃₀ (getCodeLabels '' {e | e ∈ removeTicks xs})) =
      (⋃₀ (getCodeLabels '' {e | e ∈ xs})) := by
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq]
  exact removeTicksList_labels xs

/-- Optimizing a program entry introduces no new code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "optimise_get_code_labels"]
theorem optimise_codeLabels {α : Type} (splitSeq : Bool) (limit : Nat)
    (entry : α × Nat × Bvl.Exp) :
    getCodeLabels (optimise splitSeq limit entry).2.2 ⊆ getCodeLabels entry.2.2 := by
  obtain ⟨name, arity, body⟩ := entry
  simp only [optimise, BvlHandle.compileAny]
  split
  · simpa only [Set.union_empty, letOpSing_codeLabels, removeTicksSing_labels] using
      BvlHandle.Proofs.compileSeqs_codeLabels limit (letOpSing (removeTicksSing body)) none
  · simpa only [letOpSing_codeLabels, removeTicksSing_labels] using
      BvlHandle.Proofs.compileExp_codeLabels limit arity (letOpSing (removeTicksSing body))


private def cacheLabels {α : Type} (code : Spt (α × Bvl.Exp)) : Set Nat :=
  ⋃₀ ((fun entry => getCodeLabels entry.2) '' {entry | entry ∈ sptToList code})

private theorem mkTick_labels (n : Nat) (e : Bvl.Exp) :
    getCodeLabels (Bvl.mkTick n e) = getCodeLabels e := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Bvl.mkTick, getCodeLabels] using ih

mutual
private theorem tickInlineSing_labels {α : Type} (code : Spt (α × Bvl.Exp)) (e : Bvl.Exp) :
    getCodeLabels (tickInlineSing code e) ⊆ getCodeLabels e ∪ cacheLabels code := by
  cases e with
  | var n => simp [tickInlineSing, getCodeLabels]
  | force loc n => simp [tickInlineSing, getCodeLabels]
  | ifThenElse x y z =>
    have hx := tickInlineSing_labels code x
    have hy := tickInlineSing_labels code y
    have hz := tickInlineSing_labels code z
    simp only [tickInlineSing, getCodeLabels, Set.subset_def, Set.mem_union] at *
    intro label; specialize hx label; specialize hy label; specialize hz label; aesop
  | «let» xs body =>
    have hx := tickInlineList_labels code xs
    have hy := tickInlineSing_labels code body
    simp only [tickInlineSing, getCodeLabels, Set.subset_def, Set.mem_union] at *
    intro label; specialize hx label; specialize hy label; aesop
  | raise x => simpa [tickInlineSing, getCodeLabels] using tickInlineSing_labels code x
  | tick x => simpa [tickInlineSing, getCodeLabels] using tickInlineSing_labels code x
  | handle x y =>
    have hx := tickInlineSing_labels code x
    have hy := tickInlineSing_labels code y
    simp only [tickInlineSing, getCodeLabels, Set.subset_def, Set.mem_union] at *
    intro label; specialize hx label; specialize hy label; aesop
  | op op xs =>
    have hx := tickInlineList_labels code xs
    simp only [tickInlineSing, getCodeLabels, Set.subset_def, Set.mem_union] at *
    intro label; specialize hx label; aesop
  | call ticks dest xs =>
    have hx := tickInlineList_labels code xs
    cases dest with
    | none =>
      simp only [tickInlineSing, getCodeLabels, Set.subset_def, Set.mem_union, Set.mem_empty_iff_false, false_or] at *
      intro label; specialize hx label; aesop
    | some name =>
      cases found : sptLookup name code with
      | none =>
        simp only [tickInlineSing, found, getCodeLabels, Set.subset_def, Set.mem_union] at *
        intro label; specialize hx label; aesop
      | some pair =>
        obtain ⟨arity, body⟩ := pair
        have hb : getCodeLabels body ⊆ cacheLabels code := by
          intro label h
          apply Set.mem_sUnion.mpr
          exact ⟨getCodeLabels body, ⟨(arity, body), (sptMemToList _ _).2 ⟨name, found⟩, rfl⟩, h⟩
        simp only [tickInlineSing, found, getCodeLabels, mkTick_labels, Set.subset_def, Set.mem_union] at *
        intro label; specialize hx label; specialize hb label; aesop
termination_by sizeOf e

private theorem tickInlineList_labels {α : Type} (code : Spt (α × Bvl.Exp)) (xs : List Bvl.Exp) :
    getCodeLabelsList (tickInlineList code xs) ⊆ getCodeLabelsList xs ∪ cacheLabels code := by
  cases xs with
  | nil => simp [tickInlineList, getCodeLabelsList]
  | cons x xs =>
    have hx := tickInlineSing_labels code x
    have hy := tickInlineList_labels code xs
    simp only [tickInlineList, getCodeLabelsList, Set.subset_def, Set.mem_union] at *
    intro label; specialize hx label; specialize hy label; aesop
termination_by sizeOf xs
end

/-- Tick inlining only introduces labels already present in the input or cache. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "tick_inline_code_labels"]
theorem tickInline_codeLabels {α : Type} (code : Spt (α × Bvl.Exp)) (xs : List Bvl.Exp) :
    (⋃₀ (getCodeLabels '' {e | e ∈ tickInline code xs})) ⊆
      (⋃₀ (getCodeLabels '' {e | e ∈ xs})) ∪
        (⋃₀ ((fun entry => getCodeLabels entry.2) '' {entry | entry ∈ sptToList code})) := by
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq]
  exact tickInlineList_labels code xs


private def programLabels (program : List (Nat × Nat × Bvl.Exp)) : Set Nat :=
  ⋃₀ ((fun entry => getCodeLabels entry.2.2) '' {entry | entry ∈ program})

private theorem cacheLabels_insert {α : Type} (name : Nat) (entry : α × Bvl.Exp)
    (cache : Spt (α × Bvl.Exp)) :
    cacheLabels (sptInsert name entry cache) ⊆ getCodeLabels entry.2 ∪ cacheLabels cache := by
  intro label h
  obtain ⟨_, ⟨value, member, rfl⟩, h⟩ := Set.mem_sUnion.mp h
  obtain ⟨key, found⟩ := (sptMemToList _ _).1 member
  by_cases same : key = name
  · subst key
    rw [sptLookup_sptInsert_same] at found
    cases found
    exact Or.inl h
  · rw [sptLookup_sptInsert_ne name key entry cache same] at found
    apply Or.inr
    exact Set.mem_sUnion.mpr ⟨getCodeLabels value.2,
      ⟨value, (sptMemToList _ _).2 ⟨key, found⟩, rfl⟩, h⟩

private theorem programLabels_cons (entry : Nat × Nat × Bvl.Exp)
    (entries : List (Nat × Nat × Bvl.Exp)) :
    programLabels (entry :: entries) = getCodeLabels entry.2.2 ∪ programLabels entries := by
  ext label
  simp [programLabels]

private theorem programLabels_reverse (entries : List (Nat × Nat × Bvl.Exp)) :
    programLabels entries.reverse = programLabels entries := by
  ext label
  simp [programLabels]

private theorem tickInlineAll_labels (limit : Nat) (program : List (Nat × Nat × Bvl.Exp))
    (cache : Spt (Nat × Bvl.Exp)) (acc : List (Nat × Nat × Bvl.Exp)) :
    programLabels (tickInlineAll limit cache program acc).2 ⊆
      programLabels program ∪ programLabels acc ∪ cacheLabels cache := by
  induction program generalizing cache acc with
  | nil =>
    simp only [tickInlineAll, programLabels_reverse]
    intro label h
    exact Or.inl (Or.inr h)
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    simp only [tickInlineAll]
    let newBody := tickInlineSing cache body
    have bodyBound : getCodeLabels newBody ⊆ getCodeLabels body ∪ cacheLabels cache :=
      tickInlineSing_labels cache body
    split
    · have cacheBound := cacheLabels_insert name (arity, newBody) cache
      have restBound := ih (sptInsert name (arity, newBody) cache) ((name, arity, newBody) :: acc)
      simp only [programLabels_cons, Set.subset_def, Set.mem_union] at *
      intro label
      specialize bodyBound label
      specialize cacheBound label
      specialize restBound label
      aesop
    · have restBound := ih cache ((name, arity, newBody) :: acc)
      simp only [programLabels_cons, Set.subset_def, Set.mem_union] at *
      intro label
      specialize bodyBound label
      specialize restBound label
      aesop

/-- Program-wide tick inlining introduces only input, accumulator or cache labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "tick_inline_all_code_labels"]
theorem tickInlineAll_codeLabels (limit : Nat) (cache : Spt (Nat × Bvl.Exp))
    (program acc : List (Nat × Nat × Bvl.Exp)) (finalCache : Spt (Nat × Bvl.Exp))
    (output : List (Nat × Nat × Bvl.Exp))
    (run : tickInlineAll limit cache program acc = (finalCache, output)) :
    (⋃₀ ((fun entry => getCodeLabels entry.2.2) '' {entry | entry ∈ output})) ⊆
      (⋃₀ ((fun entry => getCodeLabels entry.2.2) '' {entry | entry ∈ program})) ∪
      (⋃₀ ((fun entry => getCodeLabels entry.2.2) '' {entry | entry ∈ acc})) ∪
      (⋃₀ ((fun entry => getCodeLabels entry.2) '' {entry | entry ∈ sptToList cache})) := by
  have result := tickInlineAll_labels limit program cache acc
  rw [run] at result
  exact result


private theorem optimise_programLabels (splitSeq : Bool) (limit : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) :
    programLabels (program.map (optimise splitSeq limit)) ⊆ programLabels program := by
  induction program with
  | nil => simp [programLabels]
  | cons entry rest ih =>
    simp only [List.map_cons, programLabels_cons]
    exact Set.union_subset_union (optimise_codeLabels splitSeq limit entry) ih

/-- Whole-program BVL inlining introduces no new code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "compile_prog_get_code_labels"]
theorem compileProg_codeLabels (limit : Nat) (splitSeq : Bool) (cutSize : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (inlines : Spt (Nat × Bvl.Exp))
    (output : List (Nat × Nat × Bvl.Exp))
    (run : compileProg limit splitSeq cutSize program = (inlines, output)) :
    (⋃₀ ((fun entry => getCodeLabels entry.2.2) '' {entry | entry ∈ output})) ⊆
      (⋃₀ ((fun entry => getCodeLabels entry.2.2) '' {entry | entry ∈ program})) := by
  cases inlineRun : tickInlineAll limit .ln program [] with
  | mk cache inlined =>
    have bound := tickInlineAll_codeLabels limit .ln program [] cache inlined inlineRun
    have optimised := optimise_programLabels splitSeq cutSize inlined
    simp only [compileProg, compileInc, tickCompileProg, inlineRun] at run
    cases run
    apply Set.Subset.trans optimised
    simpa [programLabels, sptToList, sptToListA] using bound

end Flapjack.Compiler.Backend.BvlInline.Proofs
