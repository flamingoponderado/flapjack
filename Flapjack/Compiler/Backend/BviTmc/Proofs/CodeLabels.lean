module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.RewriteCorrespondence
public import Flapjack.Compiler.Backend.Semantics.BviProps.CodeLabels

@[expose] public section

/-! Name preservation for the source-shaped BVI TMC pass. -/
namespace Flapjack.Compiler.Backend.BviTmc.Proofs

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_each_keeps_names"]
theorem compileEach_keepsNames (next : Nat) (xs : List (Nat × Nat × Bvi.Exp))
    (next' : Nat) (ys : List (Nat × Nat × Bvi.Exp)) (x : Nat)
    (assumptions : compileEachSource next xs = (next', ys) ∧ x ∈ xs.map Prod.fst) :
    x ∈ ys.map Prod.fst := by
  induction xs generalizing next next' ys with
  | nil => simp at assumptions
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    cases decision : compileExpSource loc next arity body with
    | none =>
      rcases tail : compileEachSource next rest with ⟨last, output⟩
      simp only [compileEachSource, decision, tail, Prod.mk.injEq, List.map_cons, List.mem_cons] at assumptions
      rcases assumptions with ⟨⟨rfl, rfl⟩, mem | mem⟩
      · simp [mem]
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih next last output ⟨tail, mem⟩)
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      rcases tail : compileEachSource (next + bvlToBviNamespaces) rest with ⟨last, output⟩
      simp only [compileEachSource, decision, tail, Prod.mk.injEq, List.map_cons, List.mem_cons] at assumptions
      rcases assumptions with ⟨⟨rfl, rfl⟩, mem | mem⟩
      · simp [mem]
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inr (Or.inr (ih (next + bvlToBviNamespaces) last output ⟨tail, mem⟩))

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_prog_keeps_names"]
theorem compileProg_keepsNames (enabled : Bool) (next : Nat) (xs : List (Nat × Nat × Bvi.Exp))
    (next' : Nat) (ys : List (Nat × Nat × Bvi.Exp)) (x : Nat)
    (assumptions : compileProgSource enabled next xs = (next', ys) ∧ x ∈ xs.map Prod.fst) :
    x ∈ ys.map Prod.fst := by
  cases enabled with
  | false =>
    simp only [compileProgSource, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at assumptions
    simpa [← assumptions.1.2] using assumptions.2
  | true =>
    simp only [compileProgSource, ↓reduceIte] at assumptions
    exact compileEach_keepsNames next xs next' ys x assumptions

open Flapjack.Compiler.Backend.BviProps

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "get_code_labels_MAP_Var"]
theorem vars_getCodeLabels (vs : List Nat) :
    ⋃₀ (getCodeLabels '' {e | e ∈ vs.map Bvi.Exp.var}) = ∅ := by
  ext label
  simp [getCodeLabels]

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "cb_to_bvi_worker_aux_code_labels"]
theorem workerAux_getCodeLabels (cb : CallBlock) (dest ptr idx : Nat) :
    getCodeLabels (workerAuxSource cb dest ptr idx) = {dest} := by
  fun_induction workerAuxSource cb dest ptr idx with
  | case1 ticks args dest ptr idx =>
    ext label
    simp [optimiseCallSource, getCodeLabels, getCodeLabelsList_eq]
    rintro x (⟨a, _, rfl⟩ | rfl | rfl) h <;> simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel] at h
  | case2 tag left child right dest ptr idx ih =>
    ext label
    simp [mutConsSource, updateConsSource, getCodeLabels,
      getCodeLabelsList_eq, ClosLang.assignGetCodeLabel, ih]
    rintro x (⟨a, _, rfl⟩ | rfl | ⟨a, _, rfl⟩) h <;> simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel] at h

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "cb_to_bvi_worker_code_labels"]
theorem worker_getCodeLabels (cb : CallBlock) (dest ptr idx : Nat) :
    getCodeLabels (workerBlockSource cb dest ptr idx) = {dest} := by
  cases cb with
  | rCall ticks args =>
    ext label
    simp [workerBlockSource, optimiseCallSource, getCodeLabels, getCodeLabelsList_eq]
    rintro x (⟨a, _, rfl⟩ | rfl | rfl) h <;>
      simp [getCodeLabels] at h
  | callBlock tag left child right =>
    ext label
    simp [workerBlockSource, mutConsSource, updateConsSource, getCodeLabels,
      getCodeLabelsList_eq, ClosLang.assignGetCodeLabel, workerAux_getCodeLabels]
    rintro x (⟨a, _, rfl⟩ | rfl | ⟨a, _, rfl⟩) h <;>
      simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel] at h

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "cb_to_bvi_wrapper_code_labels"]
theorem wrapper_getCodeLabels (tag : Nat) (left : List Nat) (child : CallBlock) (right : List Nat) (dest : Nat) :
    getCodeLabels (wrapperBlockSource tag left child right dest) = {dest} := by
  ext label
  simp [wrapperBlockSource, mutConsSource, getCodeLabels,
    getCodeLabelsList_eq, ClosLang.assignGetCodeLabel, workerAux_getCodeLabels]
  rintro x (⟨a, _, rfl⟩ | rfl | ⟨a, _, rfl⟩) h <;>
    simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel] at h

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "bvi_to_cb_aux_code_labels_lemma"]
theorem extraction_getCodeLabels :
    (∀ n loc tag e bs r, extractOneSource n loc tag e = some (bs, r) →
      ⋃₀ (getCodeLabels '' {e | e ∈ bs}) ⊆ getCodeLabels e) ∧
    (∀ n loc tag es bs r, extractListSource n loc tag es = some (bs, r) →
      ⋃₀ (getCodeLabels '' {e | e ∈ bs}) ⊆ ⋃₀ (getCodeLabels '' {e | e ∈ es})) := by
  simp_rw [← getCodeLabelsList_eq]
  rw [← forall_and]
  intro n
  rw [← forall_and]
  intro loc
  apply extractOneSource.mutual_induct n loc
  all_goals intros
  all_goals simp_all [extractOneSource, extractListSource, callToBlockSource,
    getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel, Set.subset_def]
  all_goals simp_all [getCodeLabelsList_eq]
  case case3 =>
    obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›
    simp [getCodeLabels, ClosLang.assignGetCodeLabel, getCodeLabelsList_eq]
  all_goals aesop

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "bvi_to_cb_code_labels"]
theorem toBlock_getCodeLabels (n loc : Nat) (e : Bvi.Exp) (bs : List Bvi.Exp) (cb : CallBlock)
    (run : toBlockSource n loc e = some (bs, cb)) :
    ⋃₀ (getCodeLabels '' {e | e ∈ bs}) ⊆ getCodeLabels e := by
  rw [← getCodeLabelsList_eq]
  cases e <;> simp_all [toBlockSource, callToBlockSource, getCodeLabels, ClosLang.assignGetCodeLabel]
  case op op args =>
    cases op <;> simp_all
    case blockOp bop =>
      cases bop <;> simp_all
      case cons tag =>
        cases h : extractListSource n loc tag args with
        | none => simp [h] at run
        | some pair =>
          obtain ⟨es, r⟩ := pair
          cases r with
          | inl values => simp [h] at run
          | inr block =>
            simp [h] at run
            obtain ⟨rfl, rfl⟩ := run
            simpa only [← getCodeLabelsList_eq] using extraction_getCodeLabels.2 n loc tag args es (.inr block) h



end Flapjack.Compiler.Backend.BviTmc.Proofs
