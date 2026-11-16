module

import all Flapjack.HOL.Unification.UnifDef
import all Flapjack.HOL.Unification.UnifDef.WellFounded
meta import Flapjack.HolRef.UnificationTuple
meta import Flapjack.Test.UnificationTupleAttributeFixture

meta section

/-! Importing both owners with their proof bodies satisfies the audit. -/
open Lean Meta Flapjack

@[unificationTupleFixture] private def checkedOwnerFixture : Nat := 0

run_meta do
  let problems ← unificationTupleElaboratedProblems
  unless problems.isEmpty do
    throwError "checked import owners rejected: {problems}"
  unless ← Lean.Core.liftIOCore unificationTupleFixtureCalled.get do
    throwError "checked-owner attribute callback did not run"
