module

public import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
public import Flapjack.Compiler.Backend.FlatPattern.CompileTotal
public import Flapjack.Compiler.Backend.FlatToClos.Compile
public import Flapjack.Compiler.Backend.SourceToSource

@[expose] public section

/-! Source declarations through the flat stages to closure language. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Compile declarations through program lowering, flat elimination, pattern
compilation and closure lowering. The input has already passed through
`source_to_source`; use `compileCakeToClos` to include that pass. -/
def compileToClos (c : Config) (p : List AstHOL.Dec) : Config × List ClosLang.Exp :=
  let (c', flat) := compileTotal c p
  (c', FlatToClos.compileProg flat)

/-- Apply CakeML's source-to-source pass before source-to-closure compilation. -/
def compileCakeToClos (c : Config) (p : List AstHOL.Dec) : Config × List ClosLang.Exp :=
  compileToClos c (SourceToSource.compile p)

end Flapjack.Compiler.Backend.SourceToFlat
