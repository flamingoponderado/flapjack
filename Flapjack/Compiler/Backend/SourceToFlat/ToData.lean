module

public import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
public import Flapjack.Compiler.Backend.BviToData.Compile

@[expose] public section

/-! Checked composition through the data-language stage. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Continue the source-to-BVI composition through BVI-to-data
lowering and its data optimizations. This remains bounded and omits the outer
BVL/BVI optimization pipeline. -/
def compileCakeToDataBeforeOptimizationsFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × DataLang.Prog) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, start, code, next, names) ← compileCakeToBviBeforeOptimizationsFuel fuel source closure decls
  let code ← code.mapM fun (name, args, exp) => do
    let body ← BviToData.compileExpFuel fuel args exp
    pure (name, args, body)
  pure (source, closure, start, code, next, names)

/-- Continue the checked closure and BVI-inlining route through the
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
