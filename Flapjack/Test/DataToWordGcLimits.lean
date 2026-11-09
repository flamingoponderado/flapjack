import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Limits

/-! Non-overflow and architecture boundary checks for data-to-word limits. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

private def limits (heap : Nat) : DataSem.Limits :=
  ⟨heap, 12, 4, false, true, false⟩

example : limitsInv (limits 255) (some (.word (255 : BitVec 8))) 4 12 true false := by
  unfold limitsInv
  decide

/-- Even when the encoded heap length wraps to zero, the source bound rejects
an overflowing heap size. -/
example : ¬ limitsInv (limits 256) (some (.word (0 : BitVec 8))) 4 12 true false := by
  unfold limitsInv
  decide

example : ¬ limitsInv (limits 255) (some (.word (255 : BitVec 8))) 4 12 false false := by
  unfold limitsInv
  decide

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
