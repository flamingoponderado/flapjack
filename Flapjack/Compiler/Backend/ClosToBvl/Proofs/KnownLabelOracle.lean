import Mathlib.Data.List.Nodup
import Flapjack.Compiler.Backend.ClosKnown.Proofs.CodeLocations

/-! Label accounting for the incremental known-function optimizer. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosProps Flapjack.Compiler.Backend.ClosKnown

/-- The source optimizer preserves a leading integer entry marker. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "known_Op_Const"]
theorem knownOpConst (c : ClosKnown.Config) (trace : BackendCommon.Tra) (n : Nat)
    (xs : List ClosLang.Exp) (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c (.op trace (.intOp (.const (Int.ofNat n))) [] :: xs) env g =
      let (eas, next) := knownListTotal c xs env g
      ((.op trace (.intOp (.const (Int.ofNat n))) [], .int (Int.ofNat n)) :: eas, next) := by
  have marker : knownListTotal c [.op trace (.intOp (.const (Int.ofNat n))) []] env g =
      ([(.op trace (.intOp (.const (Int.ofNat n))) [], .int (Int.ofNat n))], g) := by
    simp [knownListTotal_op, knownListTotal, knownOpHOL, ClosOp.smartOp, ClosOp.smartOp']
  cases xs with
  | nil => simpa [knownListTotal] using marker
  | cons x xs =>
    rw [knownListTotal_cons_cons, marker]
    cases h : knownListTotal c (x :: xs) env g; simp [h]

end Flapjack.Compiler.Backend.ClosToBvl
