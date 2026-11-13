import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvalSim
import Flapjack.HolRef

/-! The shared qualification audit must accept the checked, imported ports
and reject declarations outside its fixed scope. This does not establish
HOL correspondence independently of the source review. -/

open Flapjack Lean Meta

private axiom maliciousSimulationAxiom : False

private theorem maliciousSimulationProof : True := False.elim maliciousSimulationAxiom

run_meta do
  let malicious ← predicateDomainAxiomProblems #[``maliciousSimulationProof]
  if malicious.isEmpty then throwError "project axiom dependency was accepted"
  for (name, theoremFlag) in
      [(`Flapjack.Compiler.Backend.ClosToBvl.evalSim, false),
       (`Flapjack.Compiler.Backend.ClosToBvl.impSemanticsEq, true)] do
    let problems ← predicateDomainDeclarationProblems name theoremFlag
    unless problems.isEmpty do throwError "qualified declaration {name} rejected: {problems}"
  let wrongName ← predicateDomainDeclarationProblems `Flapjack.Test.notEvalSim false
  if wrongName.isEmpty then throwError "out-of-scope declaration was accepted"
  let wrongKind ← predicateDomainDeclarationProblems `Flapjack.Compiler.Backend.ClosToBvl.evalSim true
  if wrongKind.isEmpty then throwError "wrong simulation declaration kind was accepted"
