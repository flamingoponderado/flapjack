module

public import Flapjack.Compiler.Inference.Unify.WorklistDecrease
public import Flapjack.Compiler.Inference.Unify.WorklistWellFounded
public import Flapjack.Compiler.Inference.Unify.Occurs.WorklistTotal

@[expose] public section

/-! Termination and source-shaped tail-recursion for the executed unifier. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- On the original well-formedness guard, the executed partial unifier terminates
    and returns the selected source-shaped tail-recursive result. This is
    Flapjack execution infrastructure: HOL does not have the outer Option
    used to represent nontermination here. -/
theorem unifyWorkPartialMatchesTail : ∀ (p : Spt InferT × List (List InferT × List InferT)),
    cwfs p.1 → unifyWorkPartial p.1 p.2 =
      some (Flapjack.HOL.tailRecModel cunifyCodeModel p) := by
  have wf : WellFounded worklistR := wfKcunifywlR
  intro p
  induction p using wf.induction with
  | h p ih =>
    rcases p with ⟨s, work⟩
    intro hw
    rw [Flapjack.HOL.tailRecModelEq]
    cases work with
    | nil => simp [unifyWorkPartial.eq_1, Flapjack.HOL.tailCall, cunifyCodeModel]
    | cons pair rest =>
      obtain ⟨left, right⟩ := pair
      cases left with
      | nil =>
        cases right with
        | nil =>
          rw [unifyWorkPartial.eq_2]
          simp only [Flapjack.HOL.tailCall, cunifyCodeModel]
          apply ih (s, rest)
          · exact kcunifywlEnsuresDecreaseModel _ _ ⟨hw, rfl⟩
          · exact hw
        | cons b bs => simp [unifyWorkPartial.eq_3, Flapjack.HOL.tailCall, cunifyCodeModel]
      | cons a as' =>
        cases right with
        | nil => simp [unifyWorkPartial.eq_4, Flapjack.HOL.tailCall, cunifyCodeModel]
        | cons b bs =>
          have recur : ∀ q, cunifyCodeModel (s, (a :: as', b :: bs) :: rest) = .inl q →
              unifyWorkPartial q.1 q.2 = some (Flapjack.HOL.tailRecModel cunifyCodeModel q) := by
            intro q hstep
            apply ih q (kcunifywlEnsuresDecreaseModel q _ ⟨hw, hstep⟩)
            exact kcunifywlPreservesPrecondModel _ _ ⟨hw, hstep⟩
          have wa := walkExecutableCorrect s hw a
          rw [tcwalkCorrectModel s a hw] at wa
          have wb := walkExecutableCorrect s hw b
          rw [tcwalkCorrectModel s b hw] at wb
          rw [unifyWorkPartial.eq_5, wa, wb]
          cases ha : tcwalkModel s a <;> cases hb : tcwalkModel s b <;>
            simp [Flapjack.HOL.tailCall, cunifyCodeModel, ha, hb]
          case varDb.varDb | app.app =>
            split
            · simp only
              apply recur (_, _)
              simp_all [cunifyCodeModel]
            · rfl
          case varDb.uvar | uvar.varDb =>
            apply recur (_, _)
            simp [cunifyCodeModel, ha, hb]
          case uvar.uvar =>
            rename_i v1 v2
            by_cases eq : v1 = v2
            · simp [eq]
              apply recur (_, _)
              simp [cunifyCodeModel, ha, hb, eq]
            · simp [eq]
              apply recur (_, _)
              simp [cunifyCodeModel, ha, hb, eq]
          case app.uvar =>
            rename_i ts tc v
            rw [occursWorkListMatchesModel s v ts hw]
            cases h : tcocwlModel s v [ts] <;> simp
            apply recur (_, _)
            simp [cunifyCodeModel, ha, hb, h]
          case uvar.app =>
            rename_i v ts tc
            rw [occursWorkListMatchesModel s v ts hw]
            cases h : tcocwlModel s v [ts] <;> simp
            apply recur (_, _)
            simp [cunifyCodeModel, ha, hb, h]

end Flapjack.Compiler.Inference.Unify
