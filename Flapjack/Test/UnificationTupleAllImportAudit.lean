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
  let source := HolRef.get? (← getEnv) `Flapjack.HOL.Unification.uREq
  unless unificationRelationReferenceValid source do
    throwError "reviewed unification relation metadata rejected"
  if unificationRelationReferenceValid none then
    throwError "missing unification relation metadata accepted"
  unless (unificationRelationMetadataProblems none (← getEnv)).size == 1 do
    throwError "missing HOL attribute registry accepted"
  let some source := source | throwError "missing unification relation reference"
  if unificationRelationReferenceValid (some { source with name := "other" }) ||
      unificationRelationReferenceValid (some { source with fmapAsFiniteSupportParameters := #["s", "sx"] }) ||
      unificationRelationReferenceValid (some { source with wordsAsTypeIndexedBitvec := true }) then
    throwError "changed unification relation metadata accepted"
