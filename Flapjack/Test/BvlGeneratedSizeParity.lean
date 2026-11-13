import Flapjack.Compiler.Backend.Bvl.GeneratedSize

/-! Original HOL observations from `bvl_to_bvi_value_rel_probe.out`.
These distinguish the HOL datatype size from the evaluator's termination weight. -/
open Flapjack.Compiler.Backend

#guard Bvl.expSizeHOL (.var 7) == 8
#guard Bvl.expSizeHOL (.force 3 5) == 9
#guard Bvl.expSizeHOL (.call 4 (some 8) [.var 2]) == 18
#guard Bvl.expSizeHOL (.op (.label 9) [.var 3]) == 16
#guard Bvl.expSizeHOL (.let [.var 4] (.tick (.var 2))) == 11
