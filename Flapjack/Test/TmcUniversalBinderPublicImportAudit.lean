module

import Flapjack.Compiler.Backend.BviTmc.Proofs.Induction
meta import Flapjack.HolRef.TmcUniversalBinder
meta import Flapjack.Test.TmcAttributeFixture

meta section

/-! In module mode, an ordinary import exposes theorem signatures without their proof bodies.
The TMC declaration audit must reject that context instead of treating the
resulting axiom stubs as checked witnesses. The corresponding positive audit
uses `import all` in `TmcUniversalBinderAudit`. -/
open Lean Meta Flapjack

run_meta do
  let name := `Flapjack.Compiler.Backend.BviTmc.Induction.hypothesis
  let problems ← tmcHypothesisDeclarationProblems name
  unless problems.any (·.contains "must be a checked theorem") do
    throwError "ordinary TMC import unexpectedly passed the checked-witness audit: {problems}"

/--
error: TMC attribute fixture: Flapjack.Compiler.Backend.BviTmc.Induction.holFmapAsFiniteSupportUniversalWitness_hypothesis_f must be a checked theorem
-/
#guard_msgs in
@[tmcFixture] private def tmcOpaqueImportFixture : Nat := 0
