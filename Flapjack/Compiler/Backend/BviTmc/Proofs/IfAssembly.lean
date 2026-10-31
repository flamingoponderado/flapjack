import Flapjack.Compiler.Backend.BviTmc.Proofs.IfWorker

/-! Assembly of the conditional TMC simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.IfAssembly
open BviTmc BviSem BvlSem ListSimulation IfSimulation IfWorker

/-- Flapjack infrastructure: conditional simulation assembled from the
condition and branch induction hypotheses. This omits the original induction
measure and safety premises and is not yet the HOL-shaped case theorem. -/
theorem evaluate_if {C F : Type} (condition yes no : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate [.ifThenElse condition yes no] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel opt f env1 env2)
    (conditionIH : ∀ r mid, evaluate [condition] env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core [condition] env2 f target r mid)
    (branchIH : ∀ branch mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      (∃ r, evaluate [condition] env1 source = (r, mid)) →
      (branch = yes ∨ branch = no) → evaluate [branch] env1 mid = (result, final) →
      envRel opt g env1 env2 → stateRel g mid t →
      Core [branch] env2 g t result final ∧
      ∀ locOpt, optimisedCode loc locOpt mid.code t.code →
        (∀ wrapper, rewriteWrapperSource loc locOpt env1.length branch = some wrapper →
          Core [wrapper] env2 g t result final) ∧
        (opt = true → ∀ holePtr c, holeHasVal g env1 env2 t.refs c →
          holeNotFinalised t.refs holePtr → holEl env1.length env2 = .refPtr false holePtr →
          WorkerCore (rewriteWorkerSource loc locOpt env1.length (env1.length + 1) env1.length branch)
            env1 env2 g t holePtr result final)) :
    Core [.ifThenElse condition yes no] env2 f target result final ∧
    ∀ locOpt, optimisedCode loc locOpt source.code target.code →
      (∀ wrapper, rewriteWrapperSource loc locOpt env1.length (.ifThenElse condition yes no) = some wrapper →
        Core [wrapper] env2 f target result final) ∧
      (opt = true → ∀ holePtr c, holeHasVal f env1 env2 target.refs c →
        holeNotFinalised target.refs holePtr → holEl env1.length env2 = .refPtr false holePtr →
        WorkerCore (rewriteWorkerSource loc locOpt env1.length (env1.length + 1) env1.length
          (.ifThenElse condition yes no)) env1 env2 f target holePtr result final) := by
  constructor
  · apply evaluate_if_core condition yes no source env1 result final opt f target env2
      run notTypeError environments conditionIH
    intro branch mid g t conditionRun selected branchRun env states
    exact (branchIH branch mid g t conditionRun selected branchRun env states).1
  · intro locOpt code
    constructor
    · intro wrapper wrapperRun
      apply evaluate_if_wrapper condition yes no wrapper source env1 result final opt f target env2
        loc locOpt run notTypeError environments code wrapperRun conditionIH
      intro branch branchTarget mid g t conditionRun selected rewritten branchRun env states nextCode
      have branches := branchIH branch mid g t conditionRun selected branchRun env states
      rcases rewritten with rewrite | rfl
      · exact (branches.2 locOpt nextCode).1 branchTarget rewrite
      · exact branches.1
    · intro optTrue holePtr c hole notFinal pointer
      have optEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
      apply evaluate_if_worker condition yes no source env1 result final f target env2 loc locOpt holePtr
        run notTypeError optEnv c hole notFinal pointer code conditionIH
      intro branch mid g t conditionRun selected branchRun env states nextHole nextNotFinal nextCode
      have branchEnv : envRel opt g env1 env2 := by simpa [optTrue] using env
      exact (branchIH branch mid g t conditionRun selected branchRun branchEnv states).2 locOpt nextCode |>.2
        optTrue holePtr c nextHole nextNotFinal pointer

end Flapjack.Compiler.Backend.BviTmc.IfAssembly
