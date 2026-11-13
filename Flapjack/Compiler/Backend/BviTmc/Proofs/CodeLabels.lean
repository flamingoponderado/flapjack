module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation
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



@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "rewrite_wrapper_code_labels"]
theorem rewriteWrapper_getCodeLabels (loc next n : Nat) (e y : Bvi.Exp)
    (h : rewriteWrapperSource loc next n e = some y) :
    getCodeLabels y ⊆ getCodeLabels e ∪ {next} := by
  fun_induction rewriteWrapperSource loc next n e generalizing y <;>
    simp_all [getCodeLabels, Set.subset_def]
  case case5 =>
    rename_i n op xs bs tag left child right run
    have bound := toBlock_getCodeLabels n loc (.op op xs) bs (.callBlock tag left child right) run
    simp only [← getCodeLabelsList_eq] at bound
    subst y
    simp_all [getCodeLabels, wrapper_getCodeLabels, Set.subset_def]
  case case3 =>
    obtain ⟨w, run, rfl⟩ := h
    simp_all [getCodeLabels]
    all_goals grind
  case case4 =>
    obtain ⟨w, run, rfl⟩ := h
    simp_all [getCodeLabels]
  case case2 =>
    rename_i n cond yes no yopt zopt decision ihyes ihno
    subst y
    cases hy : rewriteWrapperSource loc next n yes <;>
      cases hz : rewriteWrapperSource loc next n no <;>
      simp_all [getCodeLabels]
    all_goals grind

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "rewrite_worker_code_labels"]
theorem rewriteWorker_getCodeLabels (loc next ptr idx n : Nat) (e : Bvi.Exp) :
    getCodeLabels (rewriteWorkerSource loc next ptr idx n e) ⊆ getCodeLabels e ∪ {next} := by
  fun_induction rewriteWorkerSource loc next ptr idx n e <;>
    simp_all [getCodeLabels, getCodeLabelsList, fillHoleSource, updateConsSource,
      ClosLang.assignGetCodeLabel, Set.subset_def]
  case case5 =>
    rename_i ptr idx n op xs bs cb run
    have bound := toBlock_getCodeLabels n loc (.op op xs) bs cb run
    simp only [← getCodeLabelsList_eq] at bound
    simp_all [worker_getCodeLabels, getCodeLabels, ClosLang.assignGetCodeLabel, Set.subset_def]
    all_goals grind
  case case7 =>
    rename_i ptr idx n ticks dest args handler bs cb run
    have bound := toBlock_getCodeLabels n loc (.call ticks dest args handler) bs cb run
    simp only [← getCodeLabelsList_eq] at bound
    simp_all [worker_getCodeLabels, Set.subset_def]
    all_goals grind
  all_goals grind

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_exp_code_labels"]
theorem compileExp_getCodeLabels (loc next arity : Nat) (e wrapper worker : Bvi.Exp)
    (run : compileExpSource loc next arity e = some (wrapper, worker)) :
    getCodeLabels wrapper ⊆ getCodeLabels e ∪ {next} ∧
    getCodeLabels worker ⊆ getCodeLabels e ∪ {next} := by
  cases hw : rewriteWrapperSource loc next arity e with
  | none => simp [compileExpSource, hw] at run
  | some w =>
    simp [compileExpSource, hw] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨rewriteWrapper_getCodeLabels loc next arity e w hw,
      rewriteWorker_getCodeLabels loc next arity (arity + 1) arity e⟩

private def progLabels (p : List (Nat × Nat × Bvi.Exp)) : Set Nat :=
  ⋃₀ (getCodeLabels '' {e | e ∈ p.map (fun q => q.2.2)})
private def freshLabels (start finish : Nat) : Set Nat :=
  {label | ∃ k, label = start + k * bvlToBviNamespaces ∧ start + k * bvlToBviNamespaces < finish}
private theorem progLabels_cons (name arity : Nat) (body : Bvi.Exp) (tail : List (Nat × Nat × Bvi.Exp)) :
    progLabels ((name, arity, body) :: tail) = getCodeLabels body ∪ progLabels tail := by
  ext label; simp [progLabels]
private theorem freshLabels_step (start finish : Nat) :
    freshLabels (start + bvlToBviNamespaces) finish ⊆ freshLabels start finish := by
  intro label ⟨k, eq, bound⟩
  refine ⟨k + 1, ?_, ?_⟩ <;> simp only [Nat.add_mul, Nat.one_mul] <;> omega

/-- Function-list compilation preserves closure under an allowed label set. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_each_good_code_labels"]
theorem compileEach_goodCodeLabels (n : Nat) (c : List (Nat × Nat × Bvi.Exp)) (n2 : Nat)
    (c2 : List (Nat × Nat × Bvi.Exp)) (all : Set Nat)
    (assumptions : compileEachSource n c = (n2, c2) ∧
      (⋃₀ (getCodeLabels '' {e | e ∈ c.map (fun q => q.2.2)})) ⊆ all ∧
      {label | ∃ k, label = n + k * bvlToBviNamespaces ∧ n + k * bvlToBviNamespaces < n2} ⊆ all) :
    (⋃₀ (getCodeLabels '' {e | e ∈ c2.map (fun q => q.2.2)})) ⊆ all := by
  change compileEachSource n c = (n2, c2) ∧ progLabels c ⊆ all ∧ freshLabels n n2 ⊆ all at assumptions
  change progLabels c2 ⊆ all
  induction c generalizing n n2 c2 with
  | nil =>
    simp [compileEachSource, Prod.mk.injEq] at assumptions
    obtain ⟨⟨rfl, rfl⟩, _, _⟩ := assumptions
    simp [progLabels]
  | cons entry rest ih =>
    rcases entry with ⟨loc, arity, body⟩
    cases decision : compileExpSource loc n arity body with
    | none =>
      rcases tail : compileEachSource n rest with ⟨last, out⟩
      simp only [compileEachSource, decision, tail, Prod.mk.injEq] at assumptions
      rcases assumptions with ⟨⟨rfl, rfl⟩, old, fresh⟩
      simp only [progLabels_cons, Set.union_subset_iff] at old ⊢
      exact ⟨old.1, ih n last out ⟨tail, old.2, fresh⟩⟩
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      rcases tail : compileEachSource (n + bvlToBviNamespaces) rest with ⟨last, out⟩
      simp only [compileEachSource, decision, tail, Prod.mk.injEq] at assumptions
      rcases assumptions with ⟨⟨rfl, rfl⟩, old, fresh⟩
      obtain ⟨k, hk⟩ := compileEachSource_next_mono (n + bvlToBviNamespaces) last rest out tail
      have pos : 0 < bvlToBviNamespaces := by decide
      have freshNow : n ∈ all := by
        apply fresh
        exact ⟨0, by simp, by omega⟩
      have tailFresh : freshLabels (n + bvlToBviNamespaces) last ⊆ all :=
        Set.Subset.trans (freshLabels_step n last) fresh
      have bodyBound := compileExp_getCodeLabels loc n arity body wrapper worker decision
      simp only [progLabels_cons, Set.union_subset_iff] at old ⊢
      have allowed : getCodeLabels body ∪ {n} ⊆ all :=
        Set.union_subset old.1 (Set.singleton_subset_iff.mpr freshNow)
      exact ⟨bodyBound.1.trans allowed, bodyBound.2.trans allowed,
        ih (n + bvlToBviNamespaces) last out ⟨tail, old.2, tailFresh⟩⟩

/-- The whole-program pass preserves closure under an allowed label set. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_prog_good_code_labels"]
theorem compileProg_goodCodeLabels (b : Bool) (n : Nat) (c : List (Nat × Nat × Bvi.Exp)) (n2 : Nat)
    (c2 : List (Nat × Nat × Bvi.Exp)) (all : Set Nat)
    (assumptions : compileProgSource b n c = (n2, c2) ∧
      (⋃₀ (getCodeLabels '' {e | e ∈ c.map (fun q => q.2.2)})) ⊆ all ∧
      {label | ∃ k, label = n + k * bvlToBviNamespaces ∧ n + k * bvlToBviNamespaces < n2} ⊆ all) :
    (⋃₀ (getCodeLabels '' {e | e ∈ c2.map (fun q => q.2.2)})) ⊆ all := by
  cases b with
  | false =>
    simp only [compileProgSource, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at assumptions
    simpa only [← assumptions.1.2] using assumptions.2.1
  | true =>
    simp only [compileProgSource, ↓reduceIte] at assumptions
    exact compileEach_goodCodeLabels n c n2 c2 all assumptions

end Flapjack.Compiler.Backend.BviTmc.Proofs
