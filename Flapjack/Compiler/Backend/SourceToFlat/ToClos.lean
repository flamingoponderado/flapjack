import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatPattern.Compile
import Flapjack.Compiler.Backend.FlatToClos.Compile
import Flapjack.Compiler.Backend.SourceToSource

/-! Source declarations through the bounded flat stages to closure language. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

private def compilePatternsFuel (fuel : Nat) (cfg : FlatPattern.Config) :
    List FlatLang.Exp → Option (List FlatLang.Exp)
  | [] => some []
  | e :: es => do
      let e' ← FlatPattern.compileDecFuel fuel cfg e
      let es' ← compilePatternsFuel fuel cfg es
      pure (e' :: es')

/-- Compile declarations through program lowering, flat elimination, pattern
compilation and closure lowering. `none` reports an exhausted bounded analysis.
This entry takes declarations after `source_to_source`; use
`compileCakeToClosFuel` to include it. Proofs of sufficient bounds, subsequent
closure/backend passes and end-to-end output parity remain open. -/
def compileToClosFuel (fuel : Nat) (c : Config) (p : List AstHOL.Dec) :
    Option (Config × List ClosLang.Exp) := do
  let (c', flat) ← compileProgElim c p
  let patterns ← compilePatternsFuel fuel c'.patternCfg flat
  pure (c', FlatToClos.compileProg patterns)

/-- Apply CakeML's source-to-source pass before the bounded source-to-closure
pipeline. The later closure/backend passes and sufficient-bound proofs remain
open. -/
def compileCakeToClosFuel (fuel : Nat) (c : Config) (p : List AstHOL.Dec) :
    Option (Config × List ClosLang.Exp) :=
  compileToClosFuel fuel c (SourceToSource.compile p)

end Flapjack.Compiler.Backend.SourceToFlat
