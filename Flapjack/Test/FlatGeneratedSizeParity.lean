import Flapjack.Compiler.Backend.FlatLang.GeneratedSize

/-! Ground results from the original HOL evaluations recorded in
`scripts/hol-probes/flat_elim_value_globals_probe.out`. -/

namespace Flapjack.Test.FlatGeneratedSizeParity

open Flapjack.Compiler.Backend.FlatLang
open Flapjack.Compiler.Backend.BackendCommon

example : opSizeHOL (.src (.shift .w64 .ror 42)) = 44 := by decide
example : opSizeHOL (.tagLenEq 3 5) = 9 := by decide
example : opSizeHOL .id = 0 := by decide
example : traSizeHOL (.union (.sourceLoc 1 2 3 4) (.cons .none 5)) = 18 := by decide
example : patSizeHOL (.pcon (some (2, some (3, [(4, 5)])))
    [.pany, .plit (.intLit (-2))]) = 25 := by decide

end Flapjack.Test.FlatGeneratedSizeParity
