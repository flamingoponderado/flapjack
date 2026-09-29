import Flapjack.Misc.Fp64NanRefinement

/-!
Kernel replay of the binary64 quiet-NaN refinement facts (bead
`flapjack-h29l.6.4`): the canonical quiet NaN is accepted by both `fp64` and
`HolFloat` NaN predicates, and the HOL unspecified quiet NaN refines it.
-/

namespace Flapjack.Test.Fp64NanRefinementParity

open Flapjack

example : holFp64IsNan defaultQuietNan = true := defaultQuietNan_isQuiet.1

example : holFp64IsSignalling defaultQuietNan = false := defaultQuietNan_isQuiet.2

example : holFloatRefines (holFloatSomeQnan (.fpAdd .roundTiesToEven defaultQuietNanFloat defaultQuietNanFloat)) defaultQuietNanFloat :=
  holFloatSomeQnan_refines_defaultQuietNanFloat _

example : fp64Refines defaultQuietNan defaultQuietNan := defaultQuietNan_refines_self

def runChecks : IO Bool := do
  IO.println "PASS fp64 quiet-NaN refinement relation and canonical NaN facts"
  pure true

end Flapjack.Test.Fp64NanRefinementParity
