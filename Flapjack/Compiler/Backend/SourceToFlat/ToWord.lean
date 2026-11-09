import Flapjack.Compiler.Backend.SourceToFlat.ToData
import Flapjack.Compiler.Backend.DataToWord.Total
import Flapjack.Compiler.Backend.DataToWord.Stubs
import Flapjack.Compiler.Backend.WordBignum.Generated64
import Flapjack.Compiler.Backend.WordBignum.Generate

/-! Source-to-word compositions at intermediate and configured stages. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Flapjack's checked per-function composition retains the next local label
for diagnostics. It returns `none` when an upstream pass is unsupported; it
does not add the separately generated word stubs. -/
def compileCakeToWordWithNamesAndLabelsNoOptsFuel {width : Nat} [NeZero width]
    (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (word : DataToWord.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat ×
      List (Nat × Nat × (WordLangProgHOL (BitVec width) × Nat)) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, start, code, next, names) ← compileCakeToDataBeforeOptimizationsFuel fuel source closure decls
  let code := code.map fun (name, args, body) =>
    (name, args, DataToWord.compileControl word name 2 body)
  pure (source, closure, start, code, next, names)

/-- The checked word composition without its symbol-name result. -/
def compileCakeToWordWithLabelsNoOptsFuel {width : Nat} [NeZero width]
    (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (word : DataToWord.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat ×
      List (Nat × Nat × (WordLangProgHOL (BitVec width) × Nat)) × Nat) := do
  let (source, closure, start, code, next, _) ←
    compileCakeToWordWithNamesAndLabelsNoOptsFuel fuel source closure word decls
  pure (source, closure, start, code, next)

/-- Apply the source `compile_part` arity and result projection to the checked
composition. The omitted word stubs and outer word-to-word passes are still
required for a complete compiler, and this wrapper is not a HOL port. -/
def compileCakeToWordNoOptsFuel {width : Nat} [NeZero width]
    (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (word : DataToWord.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × WordLangProgHOL (BitVec width)) × Nat) := do
  let (source, closure, start, code, next) ←
    compileCakeToWordWithLabelsNoOptsFuel fuel source closure word decls
  pure (source, closure, start, code.map fun (name, args, body, _) => (name, args + 1, body), next)

/-- Add fixed data-to-word stubs and generated 64-bit bignum stubs to the
pre-optimization source-to-word composition. This remains partial and stops before
word-to-word optimization. -/
def compileCakeToWordWithStubs64NoOptsFuel
    (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (word : DataToWord.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × WordLangProgHOL (BitVec 64)) × Nat) := do
  let (source, closure, start, code, next) ← compileCakeToWordNoOptsFuel fuel source closure word decls
  let fixed ← DataToWord.fixedStubs? word
  let bignum ← WordBignum.generateStubs 64 DataToWord.bignumLocation
  pure (source, closure, start, fixed ++ bignum ++ code, next)

/-- Continue the checked closure and BVI-inlining route to the 64-bit
word stage. Unsupported upstream operations and exhausted fuel return `none`. -/
def compileCakeToWordWithStubsAndNames64InlineFuel
    (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (word : DataToWord.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × WordLangProgHOL (BitVec 64)) × Nat ×
      Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, start, code, next, names) ← compileCakeToDataInlineFuel fuel source closure decls
  let code := code.map fun (name, args, body) =>
    (name, args + 1, (DataToWord.compileControl (width := 64) word name 2 body).1)
  let fixed ← DataToWord.fixedStubs? word
  let bignum ← WordBignum.generateStubs 64 DataToWord.bignumLocation
  pure (source, closure, start, fixed ++ bignum ++ code, next, names)

/-- Continue the checked BVL-optimized route through 64-bit word lowering.
Earlier compilation and stub generation may return `none`. -/
def compileCakeToWord64OptimizedFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (source : Config) (closure : ClosToBvl.Config) (word : DataToWord.Config)
    (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × WordLangProgHOL (BitVec 64)) × Nat ×
      Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, start, code, next, names) ←
    compileCakeToDataOptimizedFuel fuel inlineLimit cutSize splitSeq source closure decls
  let code := code.map fun (name, args, body) =>
    (name, args + 1, (DataToWord.compileControl (width := 64) word name 2 body).1)
  let fixed ← DataToWord.fixedStubs? word
  let bignum ← WordBignum.generateStubs 64 DataToWord.bignumLocation
  pure (source, closure, start, fixed ++ bignum ++ code, next, names)

/-- Continue the configured BVL/BVI pipeline through 64-bit word lowering. -/
def compileCakeToWord64ConfiguredFuel (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (bvlConfig : BvlToBvi.Config) (word : DataToWord.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × BvlToBvi.Config × List (Nat × Nat × WordLangProgHOL (BitVec 64)) ×
      Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, bvlConfig, code, names) ← compileCakeToBviConfiguredFuel fuel source closure bvlConfig decls
  let code ← code.mapM fun (name, args, body) => do
    let body ← BviToData.compileExpBounded fuel args body
    let body := DataToWord.compileControl (width := 64) word name 2 body
    pure (name, args + 1, body.1)
  let fixed ← DataToWord.fixedStubs? word
  let bignum ← WordBignum.generateStubs 64 DataToWord.bignumLocation
  pure (source, closure, bvlConfig, fixed ++ bignum ++ code, names)

end Flapjack.Compiler.Backend.SourceToFlat
