import Flapjack.Compiler.Backend.LabToTarget.Padding

namespace Flapjack.Compiler.Backend.LabToTarget

/-- Flapjack-specific list arithmetic helper for the padding proof; it is not
a port of a separately named HOL declaration. -/
private theorem lengthFlattenReplicate {α : Type} (n : Nat) (xs : List α) :
    (List.replicate n xs).flatten.length = n * xs.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

/-- The original padding length bound retains the arbitrary element carrier
and both source premises; no word representation qualifier applies. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "LENGTH_pad_bytes"]
theorem lengthPadBytes {α : Type} (bytes nop : List α) (len : Nat)
    (h : 0 < nop.length ∧ bytes.length ≤ len) :
    (padBytes bytes len nop).length = len := by
  unfold padBytes
  dsimp only
  split
  next hle => omega
  next _ =>
    rw [List.length_take, List.length_append, lengthFlattenReplicate]
    have hmul : len ≤ len * nop.length := by
      have hp : 1 ≤ nop.length := h.1
      simpa using Nat.mul_le_mul_left len hp
    omega

end Flapjack.Compiler.Backend.LabToTarget
