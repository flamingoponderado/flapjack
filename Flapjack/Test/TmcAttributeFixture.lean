module

public meta import Flapjack.HolRef.TmcUniversalBinder

public meta section

open Lean Meta Elab Command Flapjack

initialize tmcFixtureCalled : IO.Ref Bool ← IO.mkRef false

/-- Exercise the full audit from an attribute's post-declaration callback.
This fixture does not register a HOL qualifier or certify source equivalence. -/
initialize tmcFixtureAttribute : ParametricAttribute Unit ←
  registerParametricAttribute {
    name := `tmcFixture
    descr := "test TMC witness checks during attribute registration"
    getParam := fun _ _ => pure ()
    afterSet := fun _ _ => do
      let problems ← (tmcHypothesisDeclarationProblems
        `Flapjack.Compiler.Backend.BviTmc.Induction.hypothesis).run'
      for problem in problems do
        logError m!"TMC attribute fixture: {problem}"
      if problems.isEmpty then
        Lean.Core.liftIOCore (tmcFixtureCalled.set true)
  }
