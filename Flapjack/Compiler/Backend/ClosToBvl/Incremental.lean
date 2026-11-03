import Flapjack.Compiler.Backend.ClosToBvl.Prepared
import Flapjack.Compiler.Backend.ClosToBvl.ExtractName
import Flapjack.Compiler.Backend.Semantics.BvlSem.State
import Flapjack.Compiler.Backend.Semantics.ClosSem.State

/-! Checked incremental closure-to-BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Number and annotate one incremental program while updating the retained
closure configuration. The caller checks that the optional passes are
disabled before using this transformation. -/
def prepareIncNoOpts (config : Config) (program : ClosSem.Program) : Config × ClosSem.Program :=
  let (next, numbered) := ClosNumber.ignoreTable ClosNumber.compileInc config.nextLoc program
  ({ config with nextLoc := next, callState := (config.callState.1, []) },
    ClosAnnotate.compileInc numbered)

/-- Incremental closure compilation when multi-argument introduction,
known-function optimization, and direct-call conversion are disabled.
The incoming auxiliary program is retained, as in the source's disabled
passes. Other configurations fail explicitly; the unrestricted source
incremental compiler and its correspondence remain open. -/
def compileIncNoOpts? (config : Config)
    (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    Option (Config × List (Nat × Nat × Bvl.Exp)) := do
  if config.doMti || config.doCall then none else
  match config.knownConf with
  | some _ => none
  | none =>
      let (nextConfig, annotated) := prepareIncNoOpts config program
      let (start, expressions) := extractName annotated.1
      let compiled ← compileProg? config.maxApp (chainExps start expressions ++ annotated.2)
      pure (nextConfig, compiled)

/-- Incremental closure compilation with optional multi-argument introduction.
As in the source, enabling this pass discards the incoming auxiliary program;
when disabled, it preserves it. Known-function and direct-call optimization
are still rejected. The checked traversal may retry with a structural budget. -/
def compileIncMtiFuel? (fuel : Nat) (config : Config) (program : ClosSem.Program) :
    Option (Config × List (Nat × Nat × Bvl.Exp)) := do
  if config.doCall then none else
  match config.knownConf with
  | some _ => none
  | none =>
      let program ← if config.doMti then do
        let transformed ← ClosMti.compileFuel fuel true config.maxApp program.1
        pure (transformed, [])
      else pure program
      let (nextConfig, annotated) := prepareIncNoOpts config program
      let (start, expressions) := extractName annotated.1
      let compiled ← compileProg? config.maxApp (chainExps start expressions ++ annotated.2)
      pure (nextConfig, compiled)

/-- Apply the optional incremental multi-argument transformation. -/
def prepareIncMtiFuel? (fuel : Nat) (config : Config) (program : ClosSem.Program) :
    Option ClosSem.Program := do
  if config.doMti then do
    let transformed ← ClosMti.compileFuel fuel true config.maxApp program.1
    pure (transformed, [])
  else pure program

/-- Incremental closure compilation with multi-argument and direct-call
conversion. The direct-call pass starts with the retained set of locations,
discards incoming auxiliary code, and installs its newly generated code. Known
function optimization and correspondence of these traversals remain open. -/
def compileIncCallsFuel? (fuel : Nat) (config : Config) (program : ClosSem.Program) :
    Option (Config × List (Nat × Nat × Bvl.Exp)) := do
  if !config.doCall then compileIncMtiFuel? fuel config program else
  match config.knownConf with
  | some _ => none
  | none =>
      let program ← prepareIncMtiFuel? fuel config program
      let (next, numbered) := ClosNumber.ignoreTable ClosNumber.compileInc config.nextLoc program
      let (callSet, called) ← ClosCall.compileIncFuel? fuel config.callState.1 numbered
      let nextConfig := { config with nextLoc := next, callState := (callSet, []) }
      let annotated := ClosAnnotate.compileInc called
      let (start, expressions) := extractName annotated.1
      let compiled ← compileProg? config.maxApp (chainExps start expressions ++ annotated.2)
      pure (nextConfig, compiled)

/-- Checked incremental compilation with all three optional preprocessing
passes. Inlining can still exhaust fuel, and correspondence to the original
traversals and integration into the runtime compiler remain open. -/
def compileIncFuel? (fuel : Nat) (config : Config) (program : ClosSem.Program) :
    Option (Config × List (Nat × Nat × Bvl.Exp)) := do
  let program ← prepareIncMtiFuel? fuel config program
  let (next, numbered) := ClosNumber.ignoreTable ClosNumber.compileInc config.nextLoc program
  let (knownConf, known) ← ClosKnown.compileIncFuel fuel config.knownConf numbered
  let (callSet, called) ← if config.doCall then do
    ClosCall.compileIncFuel? fuel config.callState.1 known
  else pure (config.callState.1, known)
  let nextConfig := { config with nextLoc := next, knownConf := knownConf, callState := (callSet, []) }
  let annotated := ClosAnnotate.compileInc called
  let (start, expressions) := extractName annotated.1
  let compiled ← compileProg? config.maxApp (chainExps start expressions ++ annotated.2)
  pure (nextConfig, compiled)

/-- Adapt the checked full incremental path to a downstream compiler. -/
def compileIncFuelCallback {C : Type} (fuel : Nat) (downstream : BvlSem.Compiler C) :
    ClosSem.Compiler (Config × C) := fun (config, downstreamConfig) program => do
  let (nextConfig, compiled) ← compileIncFuel? fuel config program
  let (bytes, data, nextDownstream) ← downstream downstreamConfig compiled
  pure (bytes, data, (nextConfig, nextDownstream))

/-- Adapt future incremental compiler inputs to BVL oracle entries. -/
def compileIncFuelOracle {C : Type} (fuel : Nat) (oracle : Nat → (Config × C) × ClosSem.Program)
    (index : Nat) : Option (C × List (Nat × Nat × Bvl.Exp)) := do
  let entry := oracle index
  let (_, compiled) ← compileIncFuel? fuel entry.1.1 entry.2
  pure (entry.1.2, compiled)

/-- Adapt incremental direct-call conversion to a downstream compiler. -/
def compileIncCallsFuelCallback {C : Type} (fuel : Nat) (downstream : BvlSem.Compiler C) :
    ClosSem.Compiler (Config × C) := fun (config, downstreamConfig) program => do
  let (nextConfig, compiled) ← compileIncCallsFuel? fuel config program
  let (bytes, data, nextDownstream) ← downstream downstreamConfig compiled
  pure (bytes, data, (nextConfig, nextDownstream))

/-- Adapt a downstream BVL compiler into a closure compiler, passing the
updated closure configuration onward only when both stages succeed. -/
def compileIncNoOptsCallback {C : Type} (downstream : BvlSem.Compiler C) :
    ClosSem.Compiler (Config × C) := fun (config, downstreamConfig) program => do
  let (nextConfig, compiled) ← compileIncNoOpts? config program
  let (bytes, data, nextDownstream) ← downstream downstreamConfig compiled
  pure (bytes, data, (nextConfig, nextDownstream))

/-- Downstream callback adapter for the multi-argument incremental path. -/
def compileIncMtiFuelCallback {C : Type} (fuel : Nat) (downstream : BvlSem.Compiler C) :
    ClosSem.Compiler (Config × C) := fun (config, downstreamConfig) program => do
  let (nextConfig, compiled) ← compileIncMtiFuel? fuel config program
  let (bytes, data, nextDownstream) ← downstream downstreamConfig compiled
  pure (bytes, data, (nextConfig, nextDownstream))

/-- Compile one future oracle entry, retaining its downstream configuration.
An unsupported closure configuration or checked-conversion failure is
reported as `none`. -/
def compileIncNoOptsOracle {C : Type} (oracle : Nat → (Config × C) × ClosSem.Program)
    (index : Nat) : Option (C × List (Nat × Nat × Bvl.Exp)) := do
  let entry := oracle index
  let (_, compiled) ← compileIncNoOpts? entry.1.1 entry.2
  pure (entry.1.2, compiled)

/-- Oracle adapter for the multi-argument incremental path. -/
def compileIncMtiFuelOracle {C : Type} (fuel : Nat) (oracle : Nat → (Config × C) × ClosSem.Program)
    (index : Nat) : Option (C × List (Nat × Nat × Bvl.Exp)) := do
  let entry := oracle index
  let (_, compiled) ← compileIncMtiFuel? fuel entry.1.1 entry.2
  pure (entry.1.2, compiled)

/-- Oracle adapter for incremental direct-call conversion. -/
def compileIncCallsFuelOracle {C : Type} (fuel : Nat) (oracle : Nat → (Config × C) × ClosSem.Program)
    (index : Nat) : Option (C × List (Nat × Nat × Bvl.Exp)) := do
  let entry := oracle index
  let (_, compiled) ← compileIncCallsFuel? fuel entry.1.1 entry.2
  pure (entry.1.2, compiled)

end Flapjack.Compiler.Backend.ClosToBvl
