import Flapjack.Compiler.Backend.SourceToFlat.ToDataIncremental
import Flapjack.Compiler.Backend.DataToWord.Control

/-! Checked incremental CakeML source-to-word compilation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Lower each incremental data function to 64-bit word code. Incremental
compilation does not add the whole-program word stubs. Unsupported data
operations and exhausted upstream fuel return `none`; full correspondence
and later runtime compilation stages remain open. -/
def compileCakeIncToWord64Fuel (fuel : Nat)
    (config : Config × ClosToBvl.Config × BvlToBvi.Config) (word : DataToWord.Config)
    (envId : Nat × Nat) (declarations : List AstHOL.Dec) :
    Option ((Config × ClosToBvl.Config × BvlToBvi.Config) ×
      List (Nat × Nat × WordLangProgHOL (BitVec 64))) := do
  let (config, program) ← compileCakeIncToDataFuel fuel config envId declarations
  let program ← program.mapM fun (name, args, body) => do
    let (body, _) ← DataToWord.compileControl? (width := 64) word name 2 body
    pure (name, args + 1, body)
  pure (config, program)

end Flapjack.Compiler.Backend.SourceToFlat
