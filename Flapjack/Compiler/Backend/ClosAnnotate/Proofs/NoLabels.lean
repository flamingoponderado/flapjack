import Flapjack.Compiler.Backend.ClosAnnotate.Shift.OriginalEquivalence
import Flapjack.Compiler.Backend.ClosAnnotate.Free.OriginalEquivalence
import Flapjack.Compiler.Backend.ClosAnnotate.Original
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

/-! Preservation of the source no-labels predicate by closure shifting. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang ClosProps

mutual
/-- Structural singleton case for the source no-labels proof. -/
theorem shiftSing_noLabels (expression : Exp) (m l : Nat) (i : Spt Nat)
    (safe : noLabels expression) : noLabels (shiftSing expression m l i) := by
  cases expression with
  | var trace n => simp [shiftSing, noLabels]
  | ifThenElse trace a b c =>
    simp only [shiftSing, noLabels] at safe ⊢
    exact ⟨shiftSing_noLabels a m l i safe.1, shiftSing_noLabels b m l i safe.2.1,
      shiftSing_noLabels c m l i safe.2.2⟩
  | «let» trace args body =>
    simp only [shiftSing, noLabels] at safe ⊢
    exact ⟨shiftList_noLabels args m l i safe.1, shiftSing_noLabels body m (l + args.length) i safe.2⟩
  | raise trace body =>
    simpa [shiftSing, noLabels] using shiftSing_noLabels body m l i (by simpa [noLabels] using safe)
  | tick trace body =>
    simpa [shiftSing, noLabels] using shiftSing_noLabels body m l i (by simpa [noLabels] using safe)
  | handle trace a b =>
    simp only [shiftSing, noLabels] at safe ⊢
    exact ⟨shiftSing_noLabels a m l i safe.1, shiftSing_noLabels b m (l + 1) i safe.2⟩
  | op trace op args =>
    simp only [shiftSing, noLabels] at safe ⊢
    exact ⟨safe.1, shiftList_noLabels args m l i safe.2⟩
  | call trace ticks dest args =>
    simpa [shiftSing, noLabels] using shiftList_noLabels args m l i (by simpa [noLabels] using safe)
  | app trace loc fn args =>
    simp only [shiftSing, noLabels] at safe ⊢
    exact ⟨shiftSing_noLabels fn m l i safe.1, shiftList_noLabels args m l i safe.2⟩
  | fn name loc vars arity body =>
    simp only [noLabels] at safe
    simpa [shiftSing, noLabels] using shiftSing_noLabels body (m + l) arity
      (shiftedEnv 0 ((vars.getD []).filter (· < m + l))) safe
  | letrec names loc vars fs body =>
    simp only [noLabels] at safe
    simpa [shiftSing, noLabels] using And.intro
      (shiftFuns_noLabels fs fs.length (m + l) (shiftedEnv 0 ((vars.getD []).filter (· < m + l))) safe.1)
      (shiftSing_noLabels body m (l + fs.length) i safe.2)
termination_by sizeOf expression

/-- Structural list case for the source no-labels proof. -/
theorem shiftList_noLabels (expressions : List Exp) (m l : Nat) (i : Spt Nat)
    (safe : noLabelsList expressions) : noLabelsList (shiftList expressions m l i) := by
  cases expressions with
  | nil => simp [shiftList, noLabelsList]
  | cons head tail =>
    simp only [noLabelsList] at safe
    simp only [shiftList, noLabelsList]
    exact ⟨shiftSing_noLabels head m l i safe.1, shiftList_noLabels tail m l i safe.2⟩
termination_by sizeOf expressions

/-- Structural recursive-group case for the source no-labels proof. -/
theorem shiftFuns_noLabels (functions : List (Nat × Exp)) (count m : Nat) (i : Spt Nat)
    (safe : noLabelsFuns functions) : noLabelsFuns (shiftFuns count m i functions) := by
  cases functions with
  | nil => simp [shiftFuns, noLabelsFuns]
  | cons entry tail =>
    cases entry with
    | mk arity body =>
      simp only [noLabelsFuns] at safe
      simp only [shiftFuns, noLabelsFuns]
      exact ⟨shiftSing_noLabels body m (arity + count) i safe.1,
        shiftFuns_noLabels tail count m i safe.2⟩
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Source shifting preserves the no-labels predicate for every expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "shift_no_Labels"]
theorem shiftSource_noLabels (expressions : List Exp) (m l : Nat) (i : Spt Nat)
    (safe : ∀ expression ∈ expressions, noLabels expression) :
    ∀ expression ∈ shiftSource expressions m l i, noLabels expression := by
  rw [shiftSource_eq_shiftList]
  exact (noLabelsList_iff _).1 (shiftList_noLabels expressions m l i ((noLabelsList_iff _).2 safe))

mutual
/-- Structural singleton case for the source free-variable no-labels proof. -/
theorem altFreeSing_noLabels (expression : Exp)
    (safe : noLabels expression) : noLabels (altFreeSing expression).1 := by
  cases expression with
  | var trace n => simp [altFreeSing, noLabels]
  | ifThenElse trace a b c =>
    simp only [noLabels] at safe
    simpa [altFreeSing, noLabels] using And.intro (altFreeSing_noLabels a safe.1)
      (And.intro (altFreeSing_noLabels b safe.2.1) (altFreeSing_noLabels c safe.2.2))
  | «let» trace args body =>
    simp only [noLabels] at safe
    have argsOk := altFreeList_noLabels args safe.1
    have bodyOk := altFreeSing_noLabels body safe.2
    have replicated : ∀ n, noLabelsList (List.replicate n (const0 trace)) := by
      intro n
      induction n with
      | zero => simp [noLabelsList]
      | succ n ih =>
        simp only [List.replicate_succ, noLabelsList]
        exact ⟨by simp [const0, noLabels, noLabelsList], ih⟩
    simp only [altFreeSing]
    split
    · simpa [noLabels] using And.intro (replicated args.length) bodyOk
    · simpa [noLabels] using And.intro argsOk bodyOk
  | raise trace body =>
    simpa [altFreeSing, noLabels] using altFreeSing_noLabels body (by simpa [noLabels] using safe)
  | tick trace body =>
    simpa [altFreeSing, noLabels] using altFreeSing_noLabels body (by simpa [noLabels] using safe)
  | handle trace a b =>
    simp only [noLabels] at safe
    simpa [altFreeSing, noLabels] using And.intro (altFreeSing_noLabels a safe.1) (altFreeSing_noLabels b safe.2)
  | op trace op args =>
    simp only [noLabels] at safe
    simpa [altFreeSing, noLabels] using And.intro safe.1 (altFreeList_noLabels args safe.2)
  | call trace ticks dest args =>
    simpa [altFreeSing, noLabels] using altFreeList_noLabels args (by simpa [noLabels] using safe)
  | app trace loc fn args =>
    simp only [noLabels] at safe
    simpa [altFreeSing, noLabels] using And.intro (altFreeSing_noLabels fn safe.1) (altFreeList_noLabels args safe.2)
  | fn name loc vars arity body =>
    simpa [altFreeSing, noLabels] using altFreeSing_noLabels body (by simpa [noLabels] using safe)
  | letrec names loc vars functions body =>
    simp only [noLabels] at safe
    simpa [altFreeSing, noLabels] using And.intro
      (altFreeFuns_noLabels functions functions.length safe.1) (altFreeSing_noLabels body safe.2)
termination_by sizeOf expression

/-- Structural list case for the source free-variable no-labels proof. -/
theorem altFreeList_noLabels (expressions : List Exp)
    (safe : noLabelsList expressions) : noLabelsList (altFreeList expressions).1 := by
  cases expressions with
  | nil => simp [altFreeList, noLabelsList]
  | cons first rest =>
    simp only [noLabelsList] at safe
    simpa [altFreeList, noLabelsList] using And.intro (altFreeSing_noLabels first safe.1) (altFreeList_noLabels rest safe.2)
termination_by sizeOf expressions

/-- Structural recursive-group case for the source free-variable no-labels proof. -/
theorem altFreeFuns_noLabels (functions : List (Nat × Exp)) (count : Nat)
    (safe : noLabelsFuns functions) : noLabelsFuns ((altFreeFuns count functions).map Prod.fst) := by
  cases functions with
  | nil => simp [altFreeFuns, noLabelsFuns]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [noLabelsFuns] at safe
      simpa [altFreeFuns, noLabelsFuns] using And.intro (altFreeSing_noLabels body safe.1)
        (altFreeFuns_noLabels rest count safe.2)
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Original free-variable discovery preserves the no-labels predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_free_no_Labels"]
theorem altFreeSource_noLabels {α β γ : Type} (expressions : List Exp) (_m : α) (_l : β) (_i : γ)
    (safe : ∀ expression ∈ expressions, noLabels expression) :
    ∀ expression ∈ (altFreeSource expressions).1, noLabels expression := by
  rw [altFreeSource_sing_eq.2.1]
  exact (noLabelsList_iff _).1 (altFreeList_noLabels expressions ((noLabelsList_iff _).2 safe))

/-- Original annotation preserves the no-labels predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "annotate_no_Labels"]
theorem annotateSource_noLabels (arity : Nat) (expressions : List Exp)
    (safe : ∀ expression ∈ expressions, noLabels expression) :
    ∀ expression ∈ annotateSource arity expressions, noLabels expression := by
  unfold annotateSource
  exact shiftSource_noLabels _ 0 arity .ln
    (altFreeSource_noLabels expressions (0 : Nat) (0 : Nat) (0 : Nat) safe)

/-- Original program annotation preserves the no-labels predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "no_Labels_ann"]
theorem compileSource_noLabels {α : Type} (program : List (α × Nat × Exp))
    (safe : ∀ expression ∈ program.map (fun entry => entry.2.2), noLabels expression) :
    ∀ expression ∈ (compileSource program).map (fun entry => entry.2.2), noLabels expression := by
  intro expression member
  simp only [compileSource, List.map_map, Function.comp_def] at member
  obtain ⟨⟨name, arity, body⟩, sourceMember, rfl⟩ := List.mem_map.mp member
  have bodySafe : noLabels body := safe body (List.mem_map.mpr ⟨(name, arity, body), sourceMember, rfl⟩)
  have annotated := annotateSource_noLabels arity [body] (by simpa using bodySafe)
  rw [(annotateSource_sing_eq arity body []).1] at annotated
  rw [(annotateSource_sing_eq arity body []).1]
  simpa [Flapjack.holHd] using annotated (annotateSing arity body) (by simp)

end Flapjack.Compiler.Backend.ClosAnnotate
