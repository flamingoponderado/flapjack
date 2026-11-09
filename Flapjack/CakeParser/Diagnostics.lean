import Flapjack.CakeParser.Frontend
import Flapjack.Compiler.Inference.Infer.Diagnostics

/-! Rendering for parse failures where the bounded parser identifies the
first unconsumed token. Other parser failure locations remain unported. -/
namespace Flapjack.CakeParser.Diagnostics
open Flapjack.Basis.Pure.MlString

/-- Render an unconsumed-token failure using the compiler driver's diagnostic
format. This is Flapjack CLI infrastructure, not a complete parser-error port. -/
def renderUnconsumedToken (fuel : Nat) (input : List HolChar) : Option (List HolChar) := do
  let loc ← Frontend.unconsumedTokenLocationFuel fuel fuel input
  let ascii (s : String) := (ofString s).explode
  pure (ascii "### ERROR: parse error\nParsing failed at " ++
    Flapjack.Compiler.Inference.Infer.Diagnostics.sourceLocation input (some loc) ++
    ascii "\nProgram exited with nonzero exit code.\n")

end Flapjack.CakeParser.Diagnostics
