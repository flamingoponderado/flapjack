import Flapjack.Compiler.Backend.Parmove.AllDistinct.Steps

namespace Flapjack.Test.ParmoveAllDistinctStepsParity
open Flapjack.Compiler.Backend.Parmove

/-- Test-only abbreviation for the destination predicate; not a HOL port. -/
private abbrev distinct {α : Type} (s : State α) : Prop :=
  (((s.1 ++ s.2.1 ++ s.2.2).map Prod.fst).filter Option.isSome).Nodup

-- Repeated scratch destinations are filtered; the RTC may have zero steps.
private def scratch : State Nat :=
  ([(none, some 2)], [(none, none)], [(none, some 3)])
example : distinct scratch := by decide +kernel
example : distinct scratch :=
  allDistinctSteps scratch scratch ⟨by decide +kernel, .refl⟩

private def first : State Nat :=
  ([(some 1, some 2)], [], [(none, some 3), (none, none)])
private def middle : State Nat :=
  ([], [(some 1, some 2)], [(none, some 3), (none, none)])
private def last : State Nat :=
  ([], [(some 1, none)], [(none, some 2), (none, some 3), (none, none)])

private theorem start : Step first middle := by
  simpa [first, middle] using
    Step.start (some 1) (some 2) [] [] [(none, some 3), (none, none)]
private theorem save : Step middle last := by
  simpa [middle, last] using
    Step.save (some 1) (some 2) [] [] [(none, some 3), (none, none)]
example : distinct first ∧ distinct middle ∧ distinct last := by decide +kernel
example : distinct last :=
  allDistinctSteps first last ⟨by decide +kernel,
    (Relation.ReflTransGen.single start).tail save⟩

-- The register carrier remains polymorphic and requires no equality instance.
example {α : Type} (a b : State α)
    (h : (((a.1 ++ a.2.1 ++ a.2.2).map Prod.fst).filter Option.isSome).Nodup)
    (steps : Steps a b) :
    (((b.1 ++ b.2.1 ++ b.2.2).map Prod.fst).filter Option.isSome).Nodup :=
  allDistinctSteps a b ⟨h, steps⟩

#print axioms allDistinctSteps
end Flapjack.Test.ParmoveAllDistinctStepsParity
