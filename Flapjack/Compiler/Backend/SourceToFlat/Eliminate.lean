import Flapjack.Compiler.Backend.SourceToFlat.CompileProg
import Flapjack.Compiler.Backend.FlatElim.Reachability
import Flapjack.Compiler.Backend.FlatPattern.CompileTotal

/-! The source-to-flat program stage followed by elimination and pattern compilation. -/

namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Compile declarations and eliminate unreachable flat expressions. The
option is retained for compatibility with callers of the formerly bounded
pass. This is not HOL's complete `compile_def`. -/
def compileProgElim (c : Config) (p : List AstHOL.Dec) : Option (Config × List FlatLang.Exp) :=
  let (c', code) := compileProg c p
  (FlatElim.removeFlatProg code).map (fun code' => (c', code'))

/-- Flat elimination followed by pattern compilation, in the original pass
order. Full cross-language review of the constituent passes remains open. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "compile_flat_def"]
def compileFlatTotal (cfg : FlatPattern.Config) (code : List FlatLang.Exp) : List FlatLang.Exp :=
  (FlatElim.removeFlatProgTotal code).map (FlatPattern.compileDec cfg)

/-- Compatibility entry point for callers of the formerly bounded pass. -/
def compileFlat (cfg : FlatPattern.Config) (code : List FlatLang.Exp) : Option (List FlatLang.Exp) :=
  some (compileFlatTotal cfg code)

/-- Complete source-to-flat pass, using the output configuration's pattern
settings. Full cross-language review of its constituent passes remains open. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "compile_def"]
def compileTotal (c : Config) (p : List AstHOL.Dec) : Config × List FlatLang.Exp :=
  let (next, code) := compileProg c p
  (next, compileFlatTotal next.patternCfg code)

/-- Compatibility entry point for callers of the formerly bounded pipeline. -/
def compile (c : Config) (p : List AstHOL.Dec) : Option (Config × List FlatLang.Exp) :=
  some (compileTotal c p)

end Flapjack.Compiler.Backend.SourceToFlat
