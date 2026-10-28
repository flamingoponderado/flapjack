import Flapjack.Compiler.Backend.SourceToFlat.CompileProg
import Flapjack.Compiler.Backend.FlatElim.Reachability
import Flapjack.Compiler.Backend.FlatPattern.CompileTotal

/-! The source-to-flat program stage followed by bounded dead-code elimination.
Pattern compilation remains necessary before flat-to-closure compilation. -/

namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Compile declarations and eliminate unreachable flat expressions. Failure
means the closure bound was exhausted; proving that cannot happen is open. This
is a partial pipeline building block, not HOL's complete `compile_def`. -/
def compileProgElim (c : Config) (p : List AstHOL.Dec) : Option (Config × List FlatLang.Exp) :=
  let (c', code) := compileProg c p
  (FlatElim.removeFlatProg code).map (fun code' => (c', code'))

/-- Flat elimination followed by pattern compilation, in the original pass
order. The option records the still-unproved elimination fuel bound. -/
def compileFlat (cfg : FlatPattern.Config) (code : List FlatLang.Exp) : Option (List FlatLang.Exp) :=
  (FlatElim.removeFlatProg code).map (List.map (FlatPattern.compileDec cfg))

/-- Whole source-to-flat compilation with explicit elimination exhaustion. -/
def compile (c : Config) (p : List AstHOL.Dec) : Option (Config × List FlatLang.Exp) :=
  let (next, code) := compileProg c p
  (compileFlat next.patternCfg code).map (fun result => (next, result))

end Flapjack.Compiler.Backend.SourceToFlat
