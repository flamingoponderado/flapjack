module

public import Flapjack.Compiler.Inference.Unify.ComputationalWf.Insert
public import Flapjack.Compiler.Inference.Unify.ComputationalWalk.ToVar

@[expose] public section

/-! Preservation for the executed unification worklist. -/

namespace Flapjack.Compiler.Inference.Unify
open Lean.Order

/-- Any successful return from the actual partial worklist preserves the
    source well-formedness invariant. The outer option represents possible
    nontermination, so this execution theorem is not tagged as a HOL result. -/
theorem unifyWorkPartialPreservesCwfs : ∀ s work sx, cwfs s →
    unifyWorkPartial s work = some (some sx) → cwfs sx := by
  apply unifyWorkPartial.fixpoint_induct
    (motive := fun f => ∀ s work sx, cwfs s → f s work = some (some sx) → cwfs sx)
  · apply admissible_pi
    intro s
    apply admissible_pi
    intro work
    apply admissible_pi
    intro sx
    apply admissible_pi
    intro hw
    exact admissible_apply (fun (_ : Spt InferT) (g : List (List InferT × List InferT) →
        Option (Option (Spt InferT))) => g work = some (some sx) → cwfs sx) s
      (admissible_apply (fun (_ : List (List InferT × List InferT))
        (x : Option (Option (Spt InferT))) => x = some (some sx) → cwfs sx) work
        (Option.admissible_eq_some (cwfs sx) (some sx)))
  · intro f ih s work sx hw result
    cases work with
    | nil =>
      simp only [Option.some.injEq] at result
      cases result
      exact hw
    | cons pair rest =>
      rcases pair with ⟨left, right⟩
      cases left with
      | nil =>
        cases right with
        | nil => exact ih s rest sx hw result
        | cons y ys => simp at result
      | cons x xs =>
        cases right with
        | nil => simp at result
        | cons y ys =>
          cases hx : walkExecutable s x with
          | none => simp [hx] at result
          | some a =>
            cases hy : walkExecutable s y with
            | none => simp [hx, hy] at result
            | some b =>
              simp only [hx, hy] at result
              cases a <;> cases b <;> simp at result
              case varDb.varDb | app.app =>
                split at result
                · exact ih _ _ sx hw result
                · simp at result
              case varDb.uvar =>
                rename_i db v
                exact ih _ _ sx (cwfsInsertTvarDb s v db
                  ⟨(walkExecutableToVar s y v ⟨hw, hy⟩).1, hw⟩) result
              case uvar.varDb =>
                rename_i v db
                exact ih _ _ sx (cwfsInsertTvarDb s v db
                  ⟨(walkExecutableToVar s x v ⟨hw, hx⟩).1, hw⟩) result
              case app.uvar =>
                rename_i ts tc v
                cases ho : occursWorkPartial s v [ts] with
                | none => simp [ho] at result
                | some b =>
                  cases b with
                  | true => simp [ho] at result
                  | false =>
                    simp [ho] at result
                    exact ih _ _ sx (cwfsInsertAppOfOccursFalse s v tc ts
                      ⟨(walkExecutableToVar s y v ⟨hw, hy⟩).1, hw, ho⟩) result
              case uvar.app =>
                rename_i v ts tc
                cases ho : occursWorkPartial s v [ts] with
                | none => simp [ho] at result
                | some b =>
                  cases b with
                  | true => simp [ho] at result
                  | false =>
                    simp [ho] at result
                    exact ih _ _ sx (cwfsInsertAppOfOccursFalse s v tc ts
                      ⟨(walkExecutableToVar s x v ⟨hw, hx⟩).1, hw, ho⟩) result
              case uvar.uvar =>
                rename_i v1 v2
                split at result
                · exact ih _ _ sx hw result
                · rename_i ne
                  have fresh1 := (walkExecutableToVar s x v1 ⟨hw, hx⟩).1
                  have fresh2 := (walkExecutableToVar s y v2 ⟨hw, hy⟩).1
                  exact ih _ _ sx (cwfsVar2Extend s v1 v2 ⟨hw, ne, fresh1, fresh2⟩) result

end Flapjack.Compiler.Inference.Unify
