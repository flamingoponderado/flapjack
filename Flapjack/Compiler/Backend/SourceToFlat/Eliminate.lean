module

public import Flapjack.Compiler.Backend.SourceToFlat.CompileProg
public import Flapjack.Compiler.Backend.FlatElim.Reachability
public import Flapjack.Compiler.Backend.FlatPattern.CompileTotal

@[expose] public section

/-! The source-to-flat program stage followed by elimination and pattern compilation. -/

namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Flat elimination followed by pattern compilation, in the original pass
order. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "compile_flat_def"]
def compileFlatTotal (cfg : FlatPattern.Config) (code : List FlatLang.Exp) : List FlatLang.Exp :=
  (FlatElim.removeFlatProgTotal code).map (FlatPattern.compileDec cfg)

/-- Complete source-to-flat pass, using the output configuration's pattern
settings. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "compile_def"]
def compileTotal (c : Config) (p : List AstHOL.Dec) : Config × List FlatLang.Exp :=
  let (next, code) := compileProg c p
  (next, compileFlatTotal next.patternCfg code)

end Flapjack.Compiler.Backend.SourceToFlat
