import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Values
import Flapjack.Compiler.Backend.BvlHandle.Proofs.HandleOk

/-! Replays the nested original observation in bvl_to_bvi_value_rel_probe.out. -/
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlToBvi.Proofs

#guard adjustBv (fun n => n + 5)
  (.block 7 [.number (-3), .refPtr true 2, .codePtr 3, .block 8 [.refPtr false 9]]) ==
  .block 7 [.number (-3), .refPtr true 7, .codePtr 84, .block 8 [.refPtr false 14]]

open Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlProps

-- The original HOL probe accepts the scoped body and rejects the free variable.
example : handleOk [.let [] (.let [.var 0] (.var 0))] := by
  simp [handleOk, letOk, isVar, bVarBound]

example : ¬ handleOk [.let [] (.let [.var 0] (.var 1))] := by
  simp [handleOk, letOk, isVar, bVarBound]
