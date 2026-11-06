import Flapjack.Compiler.Backend.SourceToFlat.ToBviIncremental
import Flapjack.Compiler.Backend.BviToData.Compile

/-! Checked incremental CakeML source-to-data compilation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Continue the incremental source-to-BVI pipeline through the same
per-function BVI-to-data conversion used by the original incremental backend.
The checked passes may fail, and cross-language correspondence and later
runtime compilation stages remain open. -/
def compileCakeIncToDataFuel (fuel : Nat)
    (config : Config × ClosToBvl.Config × BvlToBvi.Config) (envId : Nat × Nat)
    (declarations : List AstHOL.Dec) :
    Option ((Config × ClosToBvl.Config × BvlToBvi.Config) × List (Nat × Nat × DataLang.Prog)) := do
  let (config, program) ← compileCakeIncToBviFuel fuel config envId declarations
  let program ← program.mapM fun (name, args, body) => do
    pure (name, args, ← BviToData.compileExpBounded fuel args body)
  pure (config, program)

end Flapjack.Compiler.Backend.SourceToFlat
