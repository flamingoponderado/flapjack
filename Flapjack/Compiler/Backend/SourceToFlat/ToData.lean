import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
import Flapjack.Compiler.Backend.BviToData.Compile

/-! Checked composition through the data-language stage. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Continue the restricted source-to-BVI composition through BVI-to-data
lowering and its data optimizations. This remains bounded, requires disabled
closure optimizations, and omits the outer BVL/BVI optimization pipeline. -/
def compileCakeToDataNoOptsFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × DataLang.Prog) × Nat) := do
  let (source, closure, start, code, next) ← compileCakeToBviNoOptsFuel fuel source closure decls
  let code ← code.mapM fun (name, args, exp) => do
    let body ← BviToData.compileExpFuel fuel args exp
    pure (name, args, body)
  pure (source, closure, start, code, next)

end Flapjack.Compiler.Backend.SourceToFlat
