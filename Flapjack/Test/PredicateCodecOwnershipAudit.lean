import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvalSim
import Flapjack.HolRef.PredicateCodec

/-! Owner and axiom tests for the prospective codec guard. These checks are
preparatory and do not authorize a HOL qualifier. -/

open Lean Elab Command Flapjack

private noncomputable def axiomCarrier : Nat := Classical.choice ⟨0⟩

-- These deliberately trivial declarations test resolution only. Their
-- bodies are not acceptable codec or witness content for the qualifier.
namespace Flapjack.Test.PredicateCodecCurrent
private abbrev SimulationTail := Nat
private abbrev RawCode := Nat
private abbrev RawCodeSupport := Nat
private def toBroad : Nat := 0
private def ofBroad : Nat := 0
private def toBroadPredicate : Nat := 0
private def fromBroadPredicate : Nat := 0
theorem simulationPredicateRoundtrips : True := trivial
end Flapjack.Test.PredicateCodecCurrent

namespace Flapjack.Test.PredicateCodecWrongKind
private def SimulationTail : Nat := 0
private abbrev RawCode := Nat
private abbrev RawCodeSupport := Nat
private def toBroad : Nat := 0
private def ofBroad : Nat := 0
private def toBroadPredicate : Nat := 0
private def fromBroadPredicate : Nat := 0
theorem simulationPredicateRoundtrips : True := trivial
end Flapjack.Test.PredicateCodecWrongKind

run_cmd do
  let env ← getEnv
  let names ← match resolvePredicateCodec env with
    | .ok names => pure names
    | .error message => throwError "current codec did not resolve: {message}"
  unless names.size == 8 do throwError "unexpected codec declaration count"
  let competing := env.constants.toList.filter fun (name, _) =>
    privateToUserName? name == some `Flapjack.Compiler.Backend.ClosToBvl.toBroad &&
      predicateCodecDefiningModule env name != `Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvalSim
  if competing.isEmpty then throwError "missing imported competing private helper fixture"
  if (resolvePredicateCodecInModule env `Flapjack.HolRef
      `Flapjack.Compiler.Backend.ClosToBvl).isOk then
    throwError "codec was resolved from the wrong owner"
  let problems ← liftCoreM (predicateCodecAxiomProblems names)
  unless problems.isEmpty do throwError "current codec has axiom problems: {problems}"
  let combined ← liftCoreM predicateCodecOwnerAndAxiomProblems
  unless combined.isEmpty do throwError "combined owner and axiom check failed: {combined}"
  let badAxiom ← liftCoreM (predicateCodecAxiomProblems (names.set! 7 ``Classical.choice))
  if badAxiom.isEmpty then throwError "axiom dependency was accepted"
  let indirect ← liftCoreM (predicateCodecAxiomProblems (names.set! 7 ``axiomCarrier))
  if indirect.isEmpty then throwError "transitive axiom dependency was accepted"
  let missing ← liftCoreM (predicateCodecAxiomProblems (names.set! 7 `Flapjack.Test.missingPredicateCodec))
  if missing.isEmpty then throwError "missing checked declaration was accepted"
  let incomplete ← liftCoreM (predicateCodecAxiomProblems #[])
  if incomplete.isEmpty then throwError "an incomplete declaration set was accepted"
  let duplicate ← liftCoreM (predicateCodecAxiomProblems (names.set! 7 names[0]!))
  if duplicate.isEmpty then throwError "a duplicated declaration was accepted"
  let current ← match resolvePredicateCodecInModule env env.mainModule
      `Flapjack.Test.PredicateCodecCurrent with
    | .ok names => pure names
    | .error message => throwError "current-module codec did not resolve: {message}"
  unless current.size == 8 do throwError "unexpected current-module declaration count"
  let currentProblems ← liftCoreM (predicateCodecAxiomProblems current)
  unless currentProblems.isEmpty do throwError "current-module declarations failed: {currentProblems}"
  if (resolvePredicateCodecInModule env env.mainModule `Flapjack.Test.PredicateCodecWrongKind).isOk then
    throwError "a regular definition was accepted in an abbreviation slot"
