import Flapjack.Compiler.Backend.ClosNumber
import Flapjack.Compiler.Backend.Semantics.ClosProps.AppCallDests

/-! Closure numbering removes direct application and call destinations. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

mutual

private theorem renumber_anyDests (expression : Exp) (start : Nat) :
    appCallDests none [(renumber start expression).2] = ∅ := by
  cases expression with
  | var t v => simp [renumber, appCallDests]
  | ifThenElse t a b c => simp [renumber, appCallDests, renumber_anyDests a, renumber_anyDests b, renumber_anyDests c]
  | «let» t xs body => simp [renumber, appCallDests, renumberList_anyDests xs, renumber_anyDests body]
  | raise t body => simp [renumber, appCallDests, renumber_anyDests body]
  | handle t a b => simp [renumber, appCallDests, renumber_anyDests a, renumber_anyDests b]
  | tick t body => simp [renumber, appCallDests, renumber_anyDests body]
  | call t ticks loc args => simp [renumber, appCallDests, renumberList_anyDests args]
  | app t loc fn args => simp [renumber, appCallDests, renumber_anyDests fn, renumberList_anyDests args]
  | fn name loc vars arity body => simp [renumber, appCallDests, renumber_anyDests body]
  | letrec names loc vars functions body =>
    simp [renumber, appCallDests, renumberFuns_anyDests functions, renumber_anyDests body]
  | op t op args => simp [renumber, appCallDests, renumberList_anyDests args]
termination_by sizeOf expression

private theorem renumberList_anyDests (expressions : List Exp) (start : Nat) :
    appCallDests none (renumberList start expressions).2 = ∅ := by
  cases expressions with
  | nil => simp [renumberList, appCallDests]
  | cons first rest =>
    simp only [renumberList]
    rw [show (renumber start first).2 :: (renumberList (renumber start first).1 rest).2 =
      [(renumber start first).2] ++ (renumberList (renumber start first).1 rest).2 by rfl,
      appCallDests_append, renumber_anyDests, renumberList_anyDests]
    simp
termination_by sizeOf expressions

private theorem renumberFuns_anyDests (functions : List (Nat × Exp)) (start : Nat) :
    appCallDests none ((renumberFuns start functions).2.map Prod.snd) = ∅ := by
  cases functions with
  | nil => simp [renumberFuns, appCallDests]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [renumberFuns, List.map_cons]
      rw [show (renumber start body).2 ::
          ((renumberFuns (renumber start body).1 rest).2.map Prod.snd) =
        [(renumber start body).2] ++ ((renumberFuns (renumber start body).1 rest).2.map Prod.snd) by rfl,
        appCallDests_append, renumber_anyDests, renumberFuns_anyDests]
      simp
termination_by sizeOf functions
decreasing_by all_goals (subst_vars; simp_wf; omega)

end

/-- Numbering removes all direct application and call destinations. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_any_dests"]
theorem renumber_code_locs_any_dests :
    (∀ k xs n ys, renumberList k xs = (n, ys) → appCallDests none ys = ∅) ∧
    (∀ k x n y, renumber k x = (n, y) → appCallDests none [y] = ∅) := by
  constructor
  · intro k xs n ys run
    simpa [run] using renumberList_anyDests xs k
  · intro k x n y run
    simpa [run] using renumber_anyDests x k

end Flapjack.Compiler.Backend.ClosNumber
