module

import Flapjack.HOL.Unification.UnifDef.WellFounded
meta import Flapjack.HolRef.UnificationTuple
meta import Flapjack.Test.UnificationTupleAttributeFixture

meta section

/-! Ordinary module imports expose proof stubs, which must fail the audit. -/
open Lean Meta Flapjack

run_meta do
  let problems ← unificationTupleElaboratedProblems
  unless problems.any (·.contains "wrong declaration kind") do
    throwError "ordinary import unexpectedly passed the checked-owner audit: {problems}"

/--
error: unification tuple attribute fixture: Flapjack.HOL.Unification.uRWellFounded is missing or has the wrong declaration kind
---
error: unification tuple attribute fixture: Flapjack.HOL.Unification.uREq is missing or has the wrong declaration kind
---
error: unification tuple attribute fixture: Flapjack.HOL.Unification.holFmapAsFiniteSupportTupleWitness_uRWellFounded is missing or has the wrong declaration kind
---
error: unification tuple attribute fixture: Flapjack.HOL.Unification.holFmapAsFiniteSupportTupleWitness_uRWellFounded_reverse is missing or has the wrong declaration kind
---
error: unification tuple attribute fixture: Flapjack.HOL.Unification.holFmapAsFiniteSupportParamWitness_uREq_sx is missing or has the wrong declaration kind
---
error: unification tuple attribute fixture: Flapjack.HOL.Unification.holFmapAsFiniteSupportParamWitness_uREq_s is missing or has the wrong declaration kind
-/
#guard_msgs in
@[unificationTupleFixture] private def opaqueOwnerFixture : Nat := 0
