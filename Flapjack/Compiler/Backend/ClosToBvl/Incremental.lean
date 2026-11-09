module

public import Flapjack.Compiler.Backend.ClosToBvl.Prepared
public import Flapjack.Compiler.Backend.ClosToBvl.ExtractName
public import Flapjack.Compiler.Backend.Semantics.BvlSem.State
public import Flapjack.Compiler.Backend.Semantics.ClosSem.State

@[expose] public section

/-! Checked incremental closure-to-BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Apply the optional incremental multi-argument transformation. -/
def prepareIncMtiFuel? (fuel : Nat) (config : Config) (program : ClosSem.Program) :
    Option ClosSem.Program := do
  if config.doMti then do
    let transformed ← ClosMti.compileFuel fuel true config.maxApp program.1
    pure (transformed, [])
  else pure program

/-- Checked incremental compilation with all three optional preprocessing
passes. `compileIncFuel_eq_source` proves that this path returns the original
total incremental composition for every starting fuel. -/
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

end Flapjack.Compiler.Backend.ClosToBvl
