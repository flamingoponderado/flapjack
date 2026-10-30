import Flapjack.Compiler.Backend.BvlHandle.Simplify

/-! Structural equations for BVL handler simplification. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Bvl

/-- The direct-pattern implementation has exactly the original nested
recognizer equation. This is a proof helper, not a separate HOL declaration. -/
theorem makeHandle_source_equation (body handler : Exp) (depth : Nat) :
    makeHandle body handler depth =
      match destHandleRaise body with
      | some value => .let [value] (handleAdjVars 1 depth (handleSimp handler))
      | none => match destHandleLet body with
        | some (xs, next) => .let (handleSimpList xs) (makeHandle next handler (depth + xs.length))
        | none => match destHandleIf body with
          | some (.inr (condition, yes, no)) =>
            .ifThenElse (handleSimp condition) (handleSimp yes) (makeHandle no handler depth)
          | some (.inl (condition, yes, no)) =>
            .ifThenElse (handleSimp condition) (makeHandle yes handler depth) (handleSimp no)
          | none => .handle (handleSimp body) (handleAdjVars 1 depth (handleSimp handler)) := by
  cases body
  case ifThenElse condition yes no =>
    cases hc : canRaise condition <;> cases hy : canRaise yes <;> cases hn : canRaise no <;>
      simp only [makeHandle, destHandleRaise, destHandleLet, destHandleIf, hc, hy, hn,
        Bool.false_eq_true, ↓reduceIte]
  all_goals simp only [makeHandle, destHandleRaise, destHandleLet, destHandleIf]
  all_goals repeat' split <;> simp_all

/-- The source list simplifier is the map of its single-expression form. -/
theorem handleSimpList_eq_map (expressions : List Exp) :
    handleSimpList expressions = expressions.map handleSimp := by
  induction expressions with
  | nil => simp [handleSimpList]
  | cons expression rest ih => simp [handleSimpList, ih]

end Flapjack.Compiler.Backend.BvlHandle.Proofs
