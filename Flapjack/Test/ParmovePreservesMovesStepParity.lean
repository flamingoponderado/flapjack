import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Step

namespace Flapjack.Test.ParmovePreservesMovesStepParity
open Flapjack.Compiler.Backend.Parmove

-- Test-only destination predicate; the witness source can change after Save.
private abbrev present (x : Option Nat) (s : State Nat) : Prop :=
  ∃ y, (x, y) ∈ stateToList s ∧ x ≠ y

private def beforeSave : State Nat :=
  ([(some 4, some 5)], [(some 6, some 7), (some 1, some 2)], [(some 8, some 9)])
private def afterSave : State Nat :=
  ([(some 4, some 5)], [(some 6, some 7), (some 1, none)],
    [(none, some 2), (some 8, some 9)])
private theorem save : Step beforeSave afterSave := by
  simpa [beforeSave, afterSave] using
    Step.save (some 1) (some 2) [(some 4, some 5)] [(some 6, some 7)]
      [(some 8, some 9)]

-- Pending, active, changed source, and emitted membership branches.
example : present (some 4) afterSave :=
  stepPreservesMoves beforeSave afterSave save (some 4)
    (by refine ⟨some 5, ?_, ?_⟩ <;> decide +kernel)
example : present (some 6) afterSave :=
  stepPreservesMoves beforeSave afterSave save (some 6)
    (by refine ⟨some 7, ?_, ?_⟩ <;> decide +kernel)
example : present (some 1) afterSave :=
  stepPreservesMoves beforeSave afterSave save (some 1)
    (by refine ⟨some 2, ?_, ?_⟩ <;> decide +kernel)
example : present (some 8) afterSave :=
  stepPreservesMoves beforeSave afterSave save (some 8)
    (by refine ⟨some 9, ?_, ?_⟩ <;> decide +kernel)
example : (some 1, some 2) ∉ stateToList afterSave := by decide +kernel
example : (some 1, none) ∈ stateToList afterSave := by decide +kernel

-- Save also permits a scratch destination: its original source is emitted.
example : present none ([], [(none, none)], [(none, some 2)]) :=
  stepPreservesMoves ([], [(none, some 2)], [])
    ([], [(none, none)], [(none, some 2)])
    (Step.save none (some 2) [] [] []) none
    (by refine ⟨some 2, ?_, ?_⟩ <;> decide +kernel)

-- Removing a self move cannot remove the non-self witness.
example : present (some 1) ([(some 1, some 2)], [], []) :=
  stepPreservesMoves ([(some 1, some 1), (some 1, some 2)], [], [])
    ([(some 1, some 2)], [], [])
    (Step.removeSelf (some 1) [] [(some 1, some 2)] [] []) (some 1)
    (by refine ⟨some 2, ?_, ?_⟩ <;> decide +kernel)

-- The complete theorem is polymorphic and needs no equality instance.
example {α : Type} (first second : State α) (h : Step first second)
    (x : Option α) (hx : ∃ y, (x, y) ∈ stateToList first ∧ x ≠ y) :
    ∃ y, (x, y) ∈ stateToList second ∧ x ≠ y :=
  stepPreservesMoves first second h x hx

#print axioms stepPreservesMoves
end Flapjack.Test.ParmovePreservesMovesStepParity
