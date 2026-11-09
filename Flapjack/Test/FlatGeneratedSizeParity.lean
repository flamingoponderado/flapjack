import Flapjack.Compiler.Backend.Semantics.FlatSem.GeneratedSize

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

example : expSizeHOL (.letrec (.implode [102])
    [(.implode [103], .implode [120], .lit .none (.intLit 4))]
    (.app .none (.src .eval) [.lit .none (.intLit 2)])) = 17 := by decide

example : expSizeHOL (.handle (.cons .none 2)
    (.raise .none (.lit .none (.char 65)))
    [(.pref .pany, .con .none (some (2, some 3)) [])]) = 19 := by decide

example : expSizeHOL (.let_ .none (some (.implode [120]))
    (.varLocal .none (.implode [120]))
    (.if_ .none (.lit .none (.intLit 1))
      (.fn (.implode []) (.implode [121]) (.lit .none (.intLit 2)))
      (.mat .none (.lit .none (.intLit 3))
        [(.pany, .lit .none (.intLit 4))]))) = 23 := by decide

example : Flapjack.Compiler.Backend.FlatSem.valueSizeHOL
    (.vectorv [.conv (some (2, some 3)) [.loc true 4]]) = 17 := by decide

open Flapjack.Compiler.Backend.FlatSem in
example : valueSizeHOL (.closure ⟨[(.implode [97], .litv (.intLit 2))]⟩
    (.implode [120]) (.lit .none (.intLit 4))) = 12 := by decide

open Flapjack.Compiler.Backend.FlatSem in
example : valueSizeHOL (.recclosure ⟨[]⟩
    [(.implode [102], .implode [120], .lit .none (.intLit 1))] (.implode [102])) = 13 := by decide

end Flapjack.Test.FlatGeneratedSizeParity
