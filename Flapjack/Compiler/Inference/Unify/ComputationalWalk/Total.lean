module

public import Flapjack.Compiler.Inference.Unify.ComputationalWalk
public import Flapjack.Misc.OptionLeast.TailRec

@[expose] public section

/-! Total models of the source tail-recursive walker. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- A solution of the source `TAILREC` equation for the walker. On divergent
    inputs HOL leaves the chosen solution unspecified; this model chooses one. -/
noncomputable def tcvwalkModel (s : Spt InferT) (n : Nat) : InferT :=
  letI : Nonempty InferT := ⟨.uvar 0⟩
  Flapjack.HOL.tailRecModel (cvwalkCode s) n

/-- The source term-walker cases, using the selected tail-recursive solution. -/
noncomputable def tcwalkModel (s : Spt InferT) : InferT → InferT
  | .varDb n => .varDb n
  | .app ts name => .app ts name
  | .uvar n => tcvwalkModel s n

private theorem partialTailWalkCorrect (s : Spt InferT) (hw : cwfs s) (n : Nat) :
    Flapjack.HOL.tailRecPartial (cvwalkCode s) n = some (cvwalkModel s n) := by
  have htree : sptWf (sptMap encodeInferT s) = true := by
    rw [sptWfMap]
    exact hw.2
  induction n using (wfCvwalkR s n hw).induction with
  | h n ih =>
    rw [Flapjack.HOL.tailRecPartial.eq_1, cvwalkThm s n htree hw.1]
    cases found : sptLookup n s with
    | none => simp [cvwalkCode, found]
    | some t =>
      cases t with
      | varDb k => simp [cvwalkCode, found]
      | app ts tc => simp [cvwalkCode, found]
      | uvar u =>
        simp only [cvwalkCode, found]
        apply ih u
        exact cvwalkEnsuresDecrease s n u ⟨hw, by simp [cvwalkCode, found]⟩

/-- On the original well-formedness guard the tail-recursive solution agrees
    with the source-shaped walker; no premise assumes the result. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "tcvwalk_correct"]
theorem tcvwalkCorrectModel (s : Spt InferT) : ∀ x,
    cwfs s → cvwalkModel s x = tcvwalkModel s x := by
  intro x hw
  let : Nonempty InferT := ⟨.uvar 0⟩
  symm
  exact Flapjack.HOL.tailRecModelOfSome _ _ _ (partialTailWalkCorrect s hw x)

/-- On the original guard, the total source-shaped term walker and the
    first-order proof model agree. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "tcwalk_correct"]
theorem tcwalkCorrectModel (s : Spt InferT) (it : InferT) (hw : cwfs s) :
    cwalkModel s it = tcwalkModel s it := by
  rw [cwalkThm s it hw]
  cases it with
  | varDb n => rfl
  | app ts tc => rfl
  | uvar n => exact tcvwalkCorrectModel s n hw

end Flapjack.Compiler.Inference.Unify
