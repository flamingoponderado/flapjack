import Flapjack.RiscV.WordToStack
import Flapjack.Compiler.Backend.Parmove

/-! Actual optional parallel-move scheduler correspondence. The production
fuel implementation is compared to the reviewed deterministic fstep/pmov from
HOL parmoveScript, retaining first-source search, FRONT/LAST cycle splitting,
optional temporary moves and emitted reversal. These are Flapjack-specific
implementation equations, not HOL semantic theorem ports. Downstream filtering
and move materialization are deliberately separate obligations. -/

namespace Flapjack
open RiscV
namespace ProductionScheduler
abbrev Move := Compiler.Backend.Parmove.Move WordLocation

private theorem splitSource_eq (destination : Option WordLocation) (moves : List Move) :
    wordStackCakeSplitSource destination moves =
      match Compiler.Backend.Parmove.splitSource destination moves with
      | (_, []) => none
      | (pre, matched :: suffix) => some (pre, matched, suffix) := by
  induction moves with
  | nil => simp [wordStackCakeSplitSource, Compiler.Backend.Parmove.splitSource]
  | cons move moves ih =>
    simp only [wordStackCakeSplitSource, Compiler.Backend.Parmove.splitSource]
    by_cases equal : move.2 = destination
    · simp [equal]
    · simp only [equal, ↓reduceIte]
      rw [ih]
      rcases split : Compiler.Backend.Parmove.splitSource destination moves with ⟨pre, suffix⟩
      cases suffix <;> rfl

private theorem initLast_eq {α : Type} (head : Compiler.Backend.Parmove.Move α) (tail : List (Compiler.Backend.Parmove.Move α)) :
    wordStackCakeInitLast (head :: tail) = some (Compiler.Backend.Parmove.frontLast (α := α) head tail) := by
  induction tail generalizing head with
  | nil => simp [wordStackCakeInitLast, Compiler.Backend.Parmove.frontLast]
  | cons next rest ih =>
    rw [wordStackCakeInitLast.eq_def]
    simp only
    rw [ih next]
    rfl

private theorem aux_step (fuel : Nat) (pending active emitted : List Move) :
    wordStackCakeParallelOptionOrderAux (fuel + 1) pending active emitted =
      if pending = [] ∧ active = [] then some emitted.reverse
      else
        let next := Compiler.Backend.Parmove.fstep (pending, active, emitted)
        wordStackCakeParallelOptionOrderAux fuel next.1 next.2.1 next.2.2 := by
  cases active with
  | nil =>
    cases pending with
    | nil => simp [wordStackCakeParallelOptionOrderAux]
    | cons move pending =>
      rcases move with ⟨destination, source⟩
      simp only [List.cons_ne_nil, false_and, ↓reduceIte,
        wordStackCakeParallelOptionOrderAux, Compiler.Backend.Parmove.fstep]
      split <;> rfl
  | cons move active =>
    rcases move with ⟨destination, source⟩
    rw [wordStackCakeParallelOptionOrderAux.eq_def]
    simp only [List.cons_ne_nil, and_false, ↓reduceIte,
      Compiler.Backend.Parmove.fstep]
    rw [splitSource_eq]
    rcases split : Compiler.Backend.Parmove.splitSource destination pending with ⟨pre, suffix⟩
    cases suffix with
    | cons matched suffix => rfl
    | nil =>
      cases active with
      | nil => rfl
      | cons head tail =>
        rw [initLast_eq]
        simp only
        split <;> rfl

/-- Flapjack-specific bounded implementation correspondence. The only bound
is the scheduler termination measure; no output or well-formedness is assumed. -/
theorem aux_eq_pmov (fuel : Nat) (pending active emitted : List Move)
    (bounded : Compiler.Backend.Parmove.measure (pending, active, emitted) < fuel) :
    wordStackCakeParallelOptionOrderAux fuel pending active emitted =
      some (Compiler.Backend.Parmove.pmov (pending, active, emitted)).2.2.reverse := by
  induction fuel generalizing pending active emitted with
  | zero => omega
  | succ fuel ih =>
    rw [aux_step]
    by_cases finished : pending = [] ∧ active = []
    · rw [if_pos finished, Compiler.Backend.Parmove.pmov.eq_def, dif_pos finished]
    · rw [if_neg finished]
      have unfinished : pending ≠ [] ∨ active ≠ [] := by
        by_cases empty : pending = []
        · exact Or.inr (fun activeEmpty => finished ⟨empty, activeEmpty⟩)
        · exact Or.inl empty
      have decreases := Compiler.Backend.Parmove.fstep_decreases pending active emitted unfinished
      have smaller : Compiler.Backend.Parmove.measure
          (Compiler.Backend.Parmove.fstep (pending, active, emitted)) < fuel := by omega
      have schedule : Compiler.Backend.Parmove.pmov (pending, active, emitted) =
          Compiler.Backend.Parmove.pmov (Compiler.Backend.Parmove.fstep (pending, active, emitted)) := by
        rw [Compiler.Backend.Parmove.pmov.eq_def, dif_neg finished]
      rw [schedule]
      exact ih _ _ _ smaller

/-- The actual wrapper always returns the reviewed native scheduler output.
The 3*n+1 budget exceeds the initial 2*n measure for every list, including
identities and duplicate destinations. This says nothing about downstream
filtering, optional temporary materialization or complete move lowering. -/
theorem optionOrder_eq_parmove (moves : List (WordLocation × WordLocation)) :
    wordStackCakeParallelOptionOrder moves =
      some (Compiler.Backend.Parmove.parmove moves) := by
  unfold wordStackCakeParallelOptionOrder Compiler.Backend.Parmove.parmove
  apply aux_eq_pmov
  simp only [Compiler.Backend.Parmove.measure, List.length_map, List.length_nil]
  omega

end ProductionScheduler
end Flapjack
