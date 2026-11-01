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

/-- Adapt a downstream BVL compiler into a closure compiler, passing the
updated closure configuration onward only when both stages succeed. -/
def compileIncNoOptsCallback {C : Type} (downstream : BvlSem.Compiler C) :
    ClosSem.Compiler (Config × C) := fun (config, downstreamConfig) program => do
  let (nextConfig, compiled) ← compileIncNoOpts? config program
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

end Flapjack.Compiler.Backend.ClosToBvl
