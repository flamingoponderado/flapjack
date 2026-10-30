import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Values

/-! Replays the nested original observation in bvl_to_bvi_value_rel_probe.out. -/
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlToBvi.Proofs

#guard adjustBv (fun n => n + 5)
  (.block 7 [.number (-3), .refPtr true 2, .codePtr 3, .block 8 [.refPtr false 9]]) ==
  .block 7 [.number (-3), .refPtr true 7, .codePtr 84, .block 8 [.refPtr false 14]]
