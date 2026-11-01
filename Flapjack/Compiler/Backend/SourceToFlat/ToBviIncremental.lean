import Flapjack.Compiler.Backend.SourceToFlat.ToClos
import Flapjack.Compiler.Backend.ClosToBvl.ToBviIncremental

/-! Checked incremental CakeML source-to-BVI compilation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Compile a CakeML declaration batch through the incremental source,
closure, and BVL/BVI passes, retaining each pass's configuration. The source
incremental path intentionally does not perform flat elimination. Component
fuel exhaustion is reported as failure; source correspondence and the
remaining runtime compilation stages remain open. -/
def compileCakeIncToBviFuel (fuel : Nat)
    (config : Config × ClosToBvl.Config × BvlToBvi.Config) (envId : Nat × Nat)
    (declarations : List AstHOL.Dec) :
    Option ((Config × ClosToBvl.Config × BvlToBvi.Config) × List (Nat × Nat × Bvi.Exp)) := do
  let (source, flat) := incCompile envId config.1 (SourceToSource.compile declarations)
  let clos : ClosSem.Program := FlatToClos.incCompileDecs flat
  let ((closure, bvl), program) ← ClosToBvl.compileIncToBviFuel fuel (config.2.1, config.2.2) clos
  pure ((source, closure, bvl), program)

end Flapjack.Compiler.Backend.SourceToFlat
