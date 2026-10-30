import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyAux

/-! Replays captured integer and delegation observations from
`bvi_sem_state_probe.out`, with additional byte and index boundary checks. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BackendCommon

example {C F : Type} (s : BviState C F) :
    doAppAux (.intOp (.const 268435457)) [] s = some (some (.number 268435457, s)) := by
  simp [doAppAux, smallEnoughInt]

example {C F : Type} (s : BviState C F) :
    doAppAux (.intOp (.const 268435458)) [] s = none := by
  simp [doAppAux, smallEnoughInt]

example {C F : Type} (s : BviState C F) :
    doAppAux (.memOp .updateCons) [] s = some none := by
  simp [doAppAux]

example {C F : Type} (s : BviState C F) :
    doAppAux (.memOp (.refByte true)) [.number 1, .number 256] s = none := by
  simp [doAppAux, Flapjack.Compiler.Backend.ClosSem.intToByte]

example {C F : Type} (s : BviState C F) :
    doAppAux (.memOp (.mutCons 2 1)) [.number 5] s = none := by
  simp [doAppAux]
end Flapjack.Compiler.Backend.BviSem
