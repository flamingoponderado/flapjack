import Flapjack.Compiler.Backend.ClosToBvl.Incremental
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Oracle
import Flapjack.Compiler.Backend.BackendProps.StateCompiler
import Flapjack.Compiler.Backend.ClosMti.Proofs.Total
import Flapjack.Compiler.Backend.ClosMti.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosCall.Proofs.Total

/-! Correctness infrastructure for the checked incremental wrapper. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendProps

/-- The executed incremental preparation is exactly the optional
multi-argument transformation, including the auxiliary-code behavior. -/
theorem prepareIncMtiFuel_eq (fuel : Nat) (config : Config) (program : ClosSem.Program) :
    prepareIncMtiFuel? fuel config program =
      some (ClosMti.condCompileInc config.doMti config.maxApp program) := by
  cases enabled : config.doMti <;>
    simp [prepareIncMtiFuel?, ClosMti.condCompileInc, ClosMti.compileInc,
      ClosMti.compileFuel_introList, enabled]

/-- The incremental multi-argument preparation used by the checked compiler
preserves the current Lean closure observations under the pass invariants.
This does not establish correspondence of the evaluator or later passes to HOL. -/
theorem prepareIncMtiFuel_semantics {C F : Type} (fuel : Nat) (config : Config)
    (program : ClosSem.Program) (ffi : HolFfiState F) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C)
    (positive : config.doMti = true → 1 ≤ config.maxApp)
    (safe : config.doMti = true → ∀ n, (oracle n).2.2 = [] ∧
      ∀ e ∈ (oracle n).2.1, ClosProps.noMti e)
    (unary : config.doMti = true → ∀ e ∈ program.1, ClosProps.noMti e) :
    ∃ prepared, prepareIncMtiFuel? fuel config program = some prepared ∧
      ClosSem.semantics ffi config.maxApp HolFiniteMapExact.empty oracle
        (if config.doMti then pureCc (ClosMti.compileInc config.maxApp) compiler else compiler) program.1 =
      ClosSem.semantics ffi config.maxApp HolFiniteMapExact.empty
        (if config.doMti then pureCo (ClosMti.compileInc config.maxApp) ∘ oracle else oracle)
        compiler prepared.1 := by
  refine ⟨ClosMti.condCompileInc config.doMti config.maxApp program,
    prepareIncMtiFuel_eq fuel config program, ?_⟩
  have result := ClosMti.semantics_compile_candidate ffi config.maxApp config.doMti oracle compiler
    program.1 positive safe unary
  cases enabled : config.doMti with
  | false => simp [ClosMti.condCompileInc]
  | true => simpa [enabled, ClosMti.condCompileInc, ClosMti.compileInc, ClosMti.compile] using result

/-- With known-function optimization disabled, the full checked entry point
agrees with the earlier incremental wrapper. -/
theorem compileIncFuel_noKnown (fuel : Nat) (config : Config) (program : ClosSem.Program)
    (noKnown : config.knownConf = none) :
    compileIncFuel? fuel config program = compileIncCallsFuel? fuel config program := by
  cases call : config.doCall <;> cases mti : config.doMti <;>
    simp [compileIncFuel?, compileIncCallsFuel?, compileIncMtiFuel?, prepareIncMtiFuel?,
      prepareIncNoOpts, ClosKnown.compileIncFuel, noKnown, call, mti]
  cases ClosMti.compileFuel fuel true config.maxApp program.1 <;> simp

/-- Disabling direct-call conversion recovers the multi-argument wrapper. -/
theorem compileIncCallsFuel_disabled (fuel : Nat) (config : Config) (program : ClosSem.Program)
    (disabled : config.doCall = false) :
    compileIncCallsFuel? fuel config program = compileIncMtiFuel? fuel config program := by
  simp [compileIncCallsFuel?, disabled]

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

/-- Disabling multi-argument introduction recovers the earlier checked
incremental wrapper, including its handling of auxiliary code. -/
theorem compileIncMtiFuel_disabled (fuel : Nat) (config : Config) (program : ClosSem.Program)
    (disabled : config.doMti = false) :
    compileIncMtiFuel? fuel config program = compileIncNoOpts? config program := by
  simp [compileIncMtiFuel?, compileIncNoOpts?, disabled]

/-- When multi-argument introduction succeeds, the checked incremental
wrapper compiles its transformed main program and the source-prescribed empty
auxiliary program. HOL correspondence of the traversal remains open. -/
theorem compileIncMtiFuel_checked (fuel : Nat) (config : Config) (program : ClosSem.Program)
    (enabled : config.doMti = true) (noCall : config.doCall = false)
    (noKnown : config.knownConf = none) (transformed : List ClosLang.Exp)
    (mti : ClosMti.compileFuel fuel true config.maxApp program.1 = some transformed) :
    compileIncMtiFuel? fuel config program =
      some ((prepareIncNoOpts config (transformed, [])).1,
        compileInc config.maxApp (prepareIncNoOpts config (transformed, [])).2) := by
  let annotated := (prepareIncNoOpts config (transformed, [])).2
  have checked : compileProg? config.maxApp
      (chainExps (extractName annotated.1).1 (extractName annotated.1).2 ++ annotated.2) =
        some (compileInc config.maxApp annotated) := by
    simpa using compileInc_checked_eq config.maxApp annotated
  dsimp only [annotated] at checked
  simp [compileIncMtiFuel?, enabled, noCall, noKnown, mti, checked]

/-- The supported incremental wrapper succeeds for every input when known and
direct-call optimizations are disabled; the bounded multi-argument traversal
uses its proved structural retry bound. -/
theorem compileIncMtiFuel_succeeds (fuel : Nat) (config : Config) (program : ClosSem.Program)
    (noCall : config.doCall = false) (noKnown : config.knownConf = none) :
    ∃ result, compileIncMtiFuel? fuel config program = some result := by
  cases enabled : config.doMti with
  | false =>
    rw [compileIncMtiFuel_disabled fuel config program enabled]
    exact ⟨_, compileIncNoOpts_checked config program enabled noCall noKnown⟩
  | true =>
    obtain ⟨transformed, mti⟩ := ClosMti.compileFuel_succeeds fuel true config.maxApp program.1
    exact ⟨_, compileIncMtiFuel_checked fuel config program enabled noCall noKnown transformed mti⟩

/-- Direct-call conversion and checked BVL lowering have sufficient retry
bounds for any numbered incremental program. -/
theorem compileIncCallsFuel_succeeds (fuel : Nat) (config : Config) (program : ClosSem.Program)
    (noKnown : config.knownConf = none) :
    ∃ result, compileIncCallsFuel? fuel config program = some result := by
  cases call : config.doCall with
  | false =>
    rw [compileIncCallsFuel_disabled fuel config program call]
    exact compileIncMtiFuel_succeeds fuel config program call noKnown
  | true =>
    have mti : ∃ p, prepareIncMtiFuel? fuel config program = some p := by
      cases enabled : config.doMti with
      | false => exact ⟨program, by simp [prepareIncMtiFuel?, enabled]⟩
      | true =>
        obtain ⟨p, hp⟩ := ClosMti.compileFuel_succeeds fuel true config.maxApp program.1
        exact ⟨(p, []), by simp [prepareIncMtiFuel?, enabled, hp]⟩
    obtain ⟨p, hp⟩ := mti
    let numbered := ClosNumber.ignoreTable ClosNumber.compileInc config.nextLoc p
    obtain ⟨⟨expressions, callState⟩, hc⟩ :=
      ClosCall.callsListBounded_succeeds fuel numbered.2.1 (config.callState.1, [])
    let annotated := ClosAnnotate.compileInc (expressions, callState.2)
    have checked : compileProg? config.maxApp
        (chainExps (extractName annotated.1).1 (extractName annotated.1).2 ++ annotated.2) =
        some (compileInc config.maxApp annotated) := by
      simpa using compileInc_checked_eq config.maxApp annotated
    dsimp only [numbered] at hc
    dsimp only [annotated] at checked
    refine ⟨({ config with nextLoc := numbered.1, callState := (callState.1, []) },
      compileInc config.maxApp annotated), ?_⟩
    simp only [compileIncCallsFuel?, call, Bool.not_true, Bool.false_eq_true, ite_false, noKnown]
    rw [hp]
    dsimp only [bind, Bind.bind, Option.bind]
    unfold ClosCall.compileIncFuel?
    rw [hc]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [checked]

/-- With multi-argument introduction disabled, the callback adapters agree. -/
theorem compileIncMtiFuelCallback_disabled {C : Type} (fuel : Nat) (downstream : BvlSem.Compiler C)
    (config : Config) (downstreamConfig : C) (program : ClosSem.Program)
    (disabled : config.doMti = false) :
    compileIncMtiFuelCallback fuel downstream (config, downstreamConfig) program =
      compileIncNoOptsCallback downstream (config, downstreamConfig) program := by
  simp [compileIncMtiFuelCallback, compileIncNoOptsCallback, compileIncMtiFuel_disabled fuel config program disabled]

/-- With multi-argument introduction disabled, the oracle adapters agree. -/
theorem compileIncMtiFuelOracle_disabled {C : Type} (fuel : Nat)
    (oracle : Nat → (Config × C) × ClosSem.Program) (index : Nat)
    (disabled : (oracle index).1.1.doMti = false) :
    compileIncMtiFuelOracle fuel oracle index = compileIncNoOptsOracle oracle index := by
  simp [compileIncMtiFuelOracle, compileIncNoOptsOracle,
    compileIncMtiFuel_disabled fuel (oracle index).1.1 (oracle index).2 disabled]

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
