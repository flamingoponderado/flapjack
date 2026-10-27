import Flapjack.Compiler.Backend.SourceToFlat.ToData
import Flapjack.Compiler.Backend.DataToWord.Control

/-! Restricted source-to-word composition. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Flapjack's checked per-function composition retains the next local label
for diagnostics. It returns `none` when an upstream pass or a data-to-word
case is unsupported; it does not add the separately generated word stubs. -/
def compileCakeToWordWithLabelsNoOptsFuel {width : Nat} [NeZero width]
    (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (word : DataToWord.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat ×
      List (Nat × Nat × (WordLangProgHOL (BitVec width) × Nat)) × Nat) := do
  let (source, closure, start, code, next) ← compileCakeToDataNoOptsFuel fuel source closure decls
  let code ← code.mapM fun (name, args, body) => do
    let compiled ← DataToWord.compileControl? word name 2 body
    pure (name, args, compiled)
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

end Flapjack.Compiler.Backend.SourceToFlat
