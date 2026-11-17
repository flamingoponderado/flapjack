module

public meta import Flapjack.HolRef.UnificationTuple

public meta section

open Lean Meta Elab Command Flapjack

initialize unificationTupleFixtureCalled : IO.Ref Bool ← IO.mkRef false

/-- Exercise the prospective bundle inside an attribute callback. This
fixture does not register a HOL qualifier or establish source correspondence. -/
initialize unificationTupleFixtureAttribute : ParametricAttribute Unit ←
  registerParametricAttribute {
    name := `unificationTupleFixture
    descr := "test unification tuple audit during attribute registration"
    getParam := fun _ _ => pure ()
    afterSet := fun _ _ => do
      let problems ← unificationTupleElaboratedProblems.run'
      for problem in problems do
        logError m!"unification tuple attribute fixture: {problem}"
      if problems.isEmpty then
        Lean.Core.liftIOCore (unificationTupleFixtureCalled.set true)
  }
