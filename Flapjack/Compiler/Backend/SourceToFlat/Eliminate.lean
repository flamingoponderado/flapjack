import Flapjack.Compiler.Backend.SourceToFlat.CompileProg
import Flapjack.Compiler.Backend.FlatElim.Reachability

/-! The source-to-flat program stage followed by bounded dead-code elimination.
Pattern compilation remains necessary before flat-to-closure compilation. -/

namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Compile declarations and eliminate unreachable flat expressions. Failure
means the closure bound was exhausted; proving that cannot happen is open. This
is a partial pipeline building block, not HOL's complete `compile_def`. -/
def compileProgElim (c : Config) (p : List AstHOL.Dec) : Option (Config × List FlatLang.Exp) :=
  let (c', code) := compileProg c p
  (FlatElim.removeFlatProg code).map (fun code' => (c', code'))

end Flapjack.Compiler.Backend.SourceToFlat
