import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
import Flapjack.Compiler.Backend.BviToData.Compile

/-! Checked composition through the data-language stage. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Continue the restricted source-to-BVI composition through BVI-to-data
lowering and its data optimizations. This remains bounded, requires disabled
closure optimizations, and omits the outer BVL/BVI optimization pipeline. -/
def compileCakeToDataWithNamesNoOptsFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × DataLang.Prog) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, start, code, next, names) ← compileCakeToBviWithNamesNoOptsFuel fuel source closure decls
  let code ← code.mapM fun (name, args, exp) => do
    let body ← BviToData.compileExpFuel fuel args exp
    pure (name, args, body)
  pure (source, closure, start, code, next, names)

/-- The restricted source-to-data composition without its symbol-name result. -/
def compileCakeToDataNoOptsFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × DataLang.Prog) × Nat) := do
  let (source, closure, start, code, next, _) ← compileCakeToDataWithNamesNoOptsFuel fuel source closure decls
  pure (source, closure, start, code, next)

/-- Continue the checked multi-argument and BVI-inlining route through the
bounded BVI-to-data pass. Other BVL/BVI optimizations remain omitted. -/
def compileCakeToDataInlineFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × DataLang.Prog) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, start, code, next, names) ← compileCakeToBviInlineFuel fuel source closure decls
  let code ← code.mapM fun (name, args, exp) => do
    let body ← BviToData.compileExpFuel fuel args exp
    pure (name, args, body)
  pure (source, closure, start, code, next, names)

/-- Lower the checked BVL-optimized and BVI-inlined route to data language. -/
def compileCakeToDataOptimizedFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (source : Config) (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × DataLang.Prog) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, start, code, next, names) ←
    compileCakeToBviOptimizedInlineFuel fuel inlineLimit cutSize splitSeq source closure decls
  let code ← code.mapM fun (name, args, exp) => do
    let body ← BviToData.compileExpFuel fuel args exp
    pure (name, args, body)
  pure (source, closure, start, code, next, names)

end Flapjack.Compiler.Backend.SourceToFlat
