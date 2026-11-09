import Flapjack.AstHOL.GeneratedSize

/-! These values were evaluated by the original HOL `ast$lit_size`; see
`scripts/hol-probes/flat_elim_value_globals_probe.out`. -/

namespace Flapjack.Test.AstLiteralGeneratedSizeParity

open Flapjack.AstHOL

example : litSizeHOL (.intLit (-42)) = 1 := by decide
example : litSizeHOL (.char 255) = 1 := by decide
example : litSizeHOL (.strLit (.implode [65, 0, 255])) = 5 := by decide
example : litSizeHOL (.word8 255) = 256 := by decide
example : litSizeHOL (.word64 4294967297) = 4294967298 := by decide
example : litSizeHOL (.float64 9223372036854775808) = 9223372036854775809 := by decide

end Flapjack.Test.AstLiteralGeneratedSizeParity
