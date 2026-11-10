module

public import Flapjack.Compiler.Backend.ClosToBvl.Incremental
public import Flapjack.Compiler.Backend.BvlToBvi.Incremental

@[expose] public section

/-! Checked incremental closure-to-BVI composition. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Compose incremental closure lowering with the configured BVL-to-BVI
pipeline, carrying the state of both passes into the next invocation. Fuel
exhaustion and component failures remain explicit; HOL correspondence and
the remaining runtime compilation stages are not established here. -/
def compileIncToBviFuel (fuel : Nat) (config : Config × BvlToBvi.Config)
    (program : ClosSem.Program) : Option ((Config × BvlToBvi.Config) × List (Nat × Nat × Bvi.Exp)) := do
  let (closure, bvl) ← compileIncFuel? fuel config.1 program
  let (bvlConfig, bvi) ← BvlToBvi.compileIncAllFuel fuel config.2 bvl
  pure ((closure, bvlConfig), bvi)

end Flapjack.Compiler.Backend.ClosToBvl
