module

public import Flapjack.Compiler.Backend.BvlConst.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BvlConst.SourceCompile

@[expose] public section

/-! Code-label bounds for constant propagation. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlProps

private def envLabels (env : List (Option Bvl.Exp)) : Set Nat :=
  {label | ∃ e, some e ∈ env ∧ label ∈ getCodeLabels e}

private theorem mem_codeLabelsList (label : Nat) (es : List Bvl.Exp) :
    label ∈ getCodeLabelsList es ↔ ∃ e ∈ es, label ∈ getCodeLabels e := by
  rw [getCodeLabelsList_eq]
  simp

private theorem compileList_eq_map (env : List (Option Bvl.Exp)) (es : List Bvl.Exp) :
    compileList env es = es.map (compileSing env) := by
  induction es with
  | nil => simp [compileList]
  | cons e es ih => simp [compileList, ih]

private theorem envLabels_extract (xs : List Bvl.Exp) (env : List (Option Bvl.Exp)) :
    envLabels (extractList xs ++ env) ⊆ envLabels env := by
  intro label ⟨e, member, labels⟩
  rcases List.mem_append.mp member with member | member
  · have empty := extractList_codeLabels xs e member
    simp [empty] at labels
  · exact ⟨e, member, labels⟩

private theorem compileList_labels (env : List (Option Bvl.Exp)) (es : List Bvl.Exp)
    (each : ∀ e ∈ es, getCodeLabels (compileSing env e) ⊆ getCodeLabels e ∪ envLabels env) :
    getCodeLabelsList (compileList env es) ⊆ getCodeLabelsList es ∪ envLabels env := by
  intro label member
  rw [compileList_eq_map, mem_codeLabelsList] at member
  obtain ⟨out, mapped, labels⟩ := member
  obtain ⟨e, original, rfl⟩ := List.mem_map.mp mapped
  rcases each e original labels with h | h
  · exact Or.inl ((mem_codeLabelsList label es).2 ⟨e, original, h⟩)
  · exact Or.inr h

private theorem deleteVar_codeLabelsList (xs : List Bvl.Exp) :
    getCodeLabelsList (xs.map deleteVar) = getCodeLabelsList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [getCodeLabelsList, deleteVar_codeLabels, ih]

private theorem compileSing_labels (env : List (Option Bvl.Exp)) (e : Bvl.Exp) :
    getCodeLabels (compileSing env e) ⊆ getCodeLabels e ∪ envLabels env := by
  cases e with
  | var index =>
    simp only [compileSing]
    split <;> simp_all [getCodeLabels, envLabels, Set.subset_def, List.getElem?_eq_some_iff]
    intro label hl
    rename_i entry
    obtain ⟨bound, entry⟩ := entry
    exact ⟨_, entry ▸ List.getElem_mem bound, hl⟩
  | ifThenElse x y z =>
    have hx := compileSing_labels env x
    have hy := compileSing_labels env y
    have hz := compileSing_labels env z
    simp only [compileSing]
    simp only [getCodeLabels, Set.subset_def, Set.mem_union] at hx hy hz ⊢
    split
    · intro label h
      rcases hy label h with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
    · intro label h
      rcases hz label h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · simp only [getCodeLabels, Set.mem_union]
      intro label h
      rcases h with (h | h) | h
      · rcases hx label h with h | h
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inr h
      · rcases hy label h with h | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inr h
      · rcases hz label h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | «let» xs body =>
    have bindings := compileList_labels env xs (fun e member => compileSing_labels env e)
    have bodyLabels := compileSing_labels (extractList (compileList env xs) ++ env) body
    have envBound := envLabels_extract (compileList env xs) env
    simp only [compileSing, getCodeLabels, deleteVar_codeLabelsList,
      Set.subset_def, Set.mem_union] at bindings bodyLabels ⊢
    intro label h
    rcases h with h | h
    · rcases bindings label h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases bodyLabels label h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (envBound h)
  | handle x y =>
    have hx := compileSing_labels env x
    have hy := compileSing_labels (none :: env) y
    simp only [compileSing, getCodeLabels, Set.subset_def, Set.mem_union] at hx hy ⊢
    intro label h
    rcases h with h | h
    · exact (hx label h).imp Or.inl id
    · rcases hy label h with h | h
      · exact Or.inl (Or.inr h)
      · right
        simpa [envLabels] using h
  | raise x =>
    simpa only [compileSing, getCodeLabels] using compileSing_labels env x
  | tick x =>
    simpa only [compileSing, getCodeLabels] using compileSing_labels env x
  | op op xs =>
    have bound := compileList_labels env xs (fun e member => compileSing_labels env e)
    simp only [compileSing, smartOp_codeLabels, ← getCodeLabelsList_eq, getCodeLabels,
      Set.subset_def, Set.mem_union] at bound ⊢
    intro label h
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases bound label h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | call t dest xs =>
    have bound := compileList_labels env xs (fun e member => compileSing_labels env e)
    simp only [compileSing, getCodeLabels, Set.subset_def, Set.mem_union] at bound ⊢
    intro label h
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases bound label h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | force loc index =>
    simp only [compileSing]
    split <;> simp [getCodeLabels]
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have h := List.sizeOf_lt_of_mem member
  all_goals omega

/-- Constant propagation introduces only labels already in the expressions or
in a present entry of the constant environment. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "compile_code_labels"]
theorem compile_codeLabels (env : List (Option Bvl.Exp)) (xs : List Bvl.Exp) :
    ⋃₀ (getCodeLabels '' {e | e ∈ BvlConst.compile env xs}) ⊆
      (⋃₀ (getCodeLabels '' {e | e ∈ xs})) ∪
        ⋃₀ (getCodeLabels '' {e | some e ∈ env}) := by
  have envEq : envLabels env = ⋃₀ (getCodeLabels '' {e | some e ∈ env}) := by
    ext label
    simp [envLabels]
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq, ← envEq]
  exact compileList_labels env xs (fun e _ => compileSing_labels env e)

/-- Compiling a single expression introduces no code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "compile_exp_code_labels"]
theorem compileExp_codeLabels (e : Bvl.Exp) :
    getCodeLabels (BvlConst.compileExp e) ⊆ getCodeLabels e := by
  have bound := compile_codeLabels [] [e]
  simpa [BvlConst.compile, compileList, BvlConst.compileExp_eq] using bound

end Flapjack.Compiler.Backend.BvlConst.Proofs
