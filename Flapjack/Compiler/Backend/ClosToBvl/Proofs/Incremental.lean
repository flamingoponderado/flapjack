import Flapjack.Compiler.Backend.ClosToBvl.Incremental
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Oracle
import Flapjack.Compiler.Backend.BackendProps.StateCompiler

/-! Correctness infrastructure for the checked incremental wrapper. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendProps

/-- With optional closure optimizations disabled, the checked wrapper
returns the numbered and annotated source-shaped incremental result and the
updated numbering state. This relates Lean implementations; full HOL
correspondence and the unrestricted incremental compiler remain open. -/
theorem compileIncNoOpts_checked (config : Config) (program : ClosSem.Program)
    (noMti : config.doMti = false) (noCall : config.doCall = false)
    (noKnown : config.knownConf = none) :
    compileIncNoOpts? config program =
      some ({ config with nextLoc := (ClosNumber.compileInc config.nextLoc program.1).1, callState := (config.callState.1, []) },
        compileInc config.maxApp
          (ClosAnnotate.compileInc ((ClosNumber.compileInc config.nextLoc program.1).2, program.2))) := by
  let annotated := ClosAnnotate.compileInc ((ClosNumber.compileInc config.nextLoc program.1).2, program.2)
  have checked : compileProg? config.maxApp
      (chainExps (extractName annotated.1).1 (extractName annotated.1).2 ++ annotated.2) =
        some (compileInc config.maxApp annotated) := by
    simpa using compileInc_checked_eq config.maxApp annotated
  dsimp only [annotated] at checked
  simp [compileIncNoOpts?, prepareIncNoOpts, noMti, noCall, noKnown, ClosNumber.ignoreTable, checked]

/-- The executable callback is the stateful numbering/annotation adapter
followed by the source-shaped closure-to-BVL converter and downstream
compiler. The disabled-pass hypotheses are required on each invocation. -/
theorem compileIncNoOptsCallback_eq {C : Type} (downstream : BvlSem.Compiler C)
    (config : Config) (downstreamConfig : C) (program : ClosSem.Program)
    (noMti : config.doMti = false) (noCall : config.doCall = false)
    (noKnown : config.knownConf = none) :
    compileIncNoOptsCallback downstream (config, downstreamConfig) program =
      stateCc prepareIncNoOpts (pureCc (compileInc config.maxApp) downstream)
        (config, downstreamConfig) program := by
  rw [compileIncNoOptsCallback, compileIncNoOpts_checked config program noMti noCall noKnown]
  simp [stateCc, pureCc, prepareIncNoOpts, ClosNumber.ignoreTable]
  split <;> simp_all

/-- Each checked oracle entry agrees with the stateful preprocessing and
pure BVL oracle transformations used in the semantics proof. -/
theorem compileIncNoOptsOracle_eq {C : Type}
    (oracle : Nat → (Config × C) × ClosSem.Program) (index : Nat)
    (noMti : (oracle index).1.1.doMti = false)
    (noCall : (oracle index).1.1.doCall = false)
    (noKnown : (oracle index).1.1.knownConf = none) :
    compileIncNoOptsOracle oracle index =
      some ((pureCo (compileInc (oracle index).1.1.maxApp) ∘ stateCo prepareIncNoOpts oracle) index) := by
  rw [compileIncNoOptsOracle, compileIncNoOpts_checked (oracle index).1.1 (oracle index).2 noMti noCall noKnown]
  simp [pureCo, stateCo, prepareIncNoOpts, ClosNumber.ignoreTable]

/-- Projecting the full closure configuration to its numbering state gives
the same annotated oracle used by the no-optimization simulation. -/
theorem prepareIncNoOpts_stateCo {C : Type}
    (oracle : Nat → (Config × C) × ClosSem.Program) :
    stateCo prepareIncNoOpts oracle =
      pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
        (fun index => (((oracle index).1.1.nextLoc, (oracle index).1.2), (oracle index).2)) := by
  funext index
  simp [stateCo, pureCo, prepareIncNoOpts, ClosNumber.ignoreTable]

end Flapjack.Compiler.Backend.ClosToBvl
