import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatPattern.Compile
import Flapjack.Compiler.Backend.FlatPattern.CompileTotal
import Flapjack.Compiler.Backend.FlatToClos.Compile
import Flapjack.Compiler.Backend.SourceToSource

/-! Source declarations through the bounded flat stages to closure language. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Compile declarations through program lowering, flat elimination, pattern
compilation and closure lowering. The option is retained for compatibility;
the flat-elimination closure bound is proved sufficient.
This entry takes declarations after `source_to_source`; use
`compileCakeToClosFuel` to include it. Proofs of subsequent closure/backend
passes and end-to-end output parity remain open. The fuel
argument is retained for callers of the former bounded pattern implementation;
pattern compilation itself is now total. -/
def compileToClosFuel (_fuel : Nat) (c : Config) (p : List AstHOL.Dec) :
    Option (Config × List ClosLang.Exp) := do
  let (c', flat) ← compile c p
  pure (c', FlatToClos.compileProg flat)

/-- Apply CakeML's source-to-source pass before the bounded source-to-closure
pipeline. Correctness of the later closure/backend passes remains open. -/
def compileCakeToClosFuel (fuel : Nat) (c : Config) (p : List AstHOL.Dec) :
    Option (Config × List ClosLang.Exp) :=
  compileToClosFuel fuel c (SourceToSource.compile p)

end Flapjack.Compiler.Backend.SourceToFlat
