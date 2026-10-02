import Flapjack.HolRef
import Lean.Elab.Tactic.Omega

/-! Counterpart of the pinned HOL state-transformer iteration definition. -/
namespace Flapjack

/-- Inclusive iteration over either direction. HOL BIND discards the unit result
and passes the resulting state to the next action; the endpoint executes once. -/
@[hol "HOL/src/monad/more_monads/state_transformerScript.sml" "FOR_def"]
def holFor {σ : Type} :
    Nat × Nat × (Nat → σ → Unit × σ) → σ → Unit × σ
  | (i, j, a) => fun s =>
    if i = j then a i s
    else
      let r := a i s
      holFor ((if i < j then i + 1 else i - 1), j, a) r.2
termination_by p => if p.1 < p.2.1 then p.2.1 - p.1 else p.1 - p.2.1
decreasing_by all_goals (simp_wf; split <;> split <;> omega)

/-- Flapjack regression: both endpoints participate in ascending traversal. -/
example : (holFor (1, 3, fun i s => ((), s ++ [i])) ([] : List Nat)) = ((), [1, 2, 3]) := by
  simp [holFor]

/-- Flapjack regression: descending traversal retains the same inclusive rule. -/
example : (holFor (3, 1, fun i s => ((), s ++ [i])) ([] : List Nat)) = ((), [3, 2, 1]) := by
  simp [holFor]

/-- Flapjack regression: equal endpoints execute exactly once, including zero. -/
example : (holFor (0, 0, fun i s => ((), s ++ [i])) ([] : List Nat)) = ((), [0]) := by
  simp [holFor]

/-- Flapjack regression: descending through zero preserves the initial state. -/
example : (holFor (2, 0, fun i s => ((), s ++ [i])) ([9] : List Nat)) = ((), [9, 2, 1, 0]) := by
  simp [holFor]

end Flapjack
