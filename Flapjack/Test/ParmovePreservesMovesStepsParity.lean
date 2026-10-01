import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Steps

namespace Flapjack.Test.ParmovePreservesMovesStepsParity
open Flapjack.Compiler.Backend.Parmove

private def first : State Nat := ([(some 1, some 2)], [], [(none, some 3)])
private def middle : State Nat := ([], [(some 1, some 2)], [(none, some 3)])
private def last : State Nat :=
  ([], [(some 1, none)], [(none, some 2), (none, some 3)])
private theorem trace : Steps first last := by
  have start : Step first middle := by
    simpa [first, middle] using Step.start (some 1) (some 2) [] [] [(none, some 3)]
  have save : Step middle last := by
    simpa [middle, last] using Step.save (some 1) (some 2) [] [] [(none, some 3)]
  exact (Relation.ReflTransGen.single start).tail save

-- Zero steps retain the original non-self witness, even a scratch destination.
example : ∃ y, (none, y) ∈ stateToList first ∧ none ≠ y :=
  stepsPreservesMoves none first first
    ⟨by refine ⟨some 3, ?_, ?_⟩ <;> decide +kernel, .refl⟩

-- Start/Save changes the source while preserving its non-self destination.
example : ∃ y, (some 1, y) ∈ stateToList last ∧ some 1 ≠ y :=
  stepsPreservesMoves (some 1) first last
    ⟨by refine ⟨some 2, ?_, ?_⟩ <;> decide +kernel, trace⟩
example : (some 1, none) ∈ stateToList last := by decide +kernel
example : (some 1, some 2) ∉ stateToList last := by decide +kernel
example : ∃ y, (none, y) ∈ stateToList last ∧ none ≠ y :=
  stepsPreservesMoves none first last
    ⟨by refine ⟨some 3, ?_, ?_⟩ <;> decide +kernel, trace⟩

-- No well-formedness or decidable-equality assumption is needed.
example {α : Type} (x : Option α) (a b : State α)
    (witness : ∃ y, (x, y) ∈ stateToList a ∧ x ≠ y) (trace : Steps a b) :
    ∃ y, (x, y) ∈ stateToList b ∧ x ≠ y :=
  stepsPreservesMoves x a b ⟨witness, trace⟩

#print axioms stepsPreservesMoves
end Flapjack.Test.ParmovePreservesMovesStepsParity
