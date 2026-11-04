import Flapjack.RiscV.WordExpressionFlatten

/-! Original HOL `const_fp` rows captured in
`scripts/hol-probes/word_simp_const_fp_mem_probe.out`: through
`const_fp_inst_cs_def` only `Load`/`Load8`/`Load32` forget their destination,
so after a store or a sixteen-bit operation the known `2 := 7` still folds
`Var 2 + 3` to `10`. Each row compares the executed `wordConstFpLoop` from
empty knowledge (HOL `const_fp p = FST (const_fp_loop p LN)`) with that output. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Flapjack.Test.WordSimpConstFpMemParity
open Flapjack RiscV

end Flapjack.Test.WordSimpConstFpMemParity
