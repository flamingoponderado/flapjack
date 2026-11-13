module

public import Flapjack.AstHOL.GeneratedSize

@[expose] public section

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

/-! Original HOL `ast$op_size` evaluations for every constructor with fields
and one of the zero-sized constructors. -/
example : opSizeHOL (.arith .add (.wordT .w8)) = 2 := by decide
example : opSizeHOL (.fromTo (.wordT .w8) (.wordT .w64)) = 3 := by decide
example : opSizeHOL (.shift .w64 .ror 42) = 43 := by decide
example : opSizeHOL (.test (.compare .lt) (.wordT .w64)) = 3 := by decide
example : opSizeHOL (.thunkOp (.allocThunk .evaluated)) = 2 := by decide
example : opSizeHOL (.ffi (.implode [65, 0, 255])) = 5 := by decide
example : opSizeHOL .eval = 0 := by decide

end Flapjack.Test.AstLiteralGeneratedSizeParity
