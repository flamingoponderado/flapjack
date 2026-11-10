module

public import Mathlib.Data.List.Nodup
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CodeLocations
public import Flapjack.Compiler.Backend.ClosTicks.Source
public import Flapjack.Compiler.Backend.ClosLetop.Source

@[expose] public section

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

/-- Tick removal leaves a leading nonnegative integer entry marker unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "remove_ticks_Op_Const"]
theorem removeTicks_opConst (trace : BackendCommon.Tra) (n : Nat) (xs : List ClosLang.Exp) :
    ClosTicks.removeList (.op trace (.intOp (.const (Int.ofNat n))) [] :: xs) =
      .op trace (.intOp (.const (Int.ofNat n))) [] :: ClosTicks.removeList xs := by
  rfl

/-- Let-operation cleanup leaves a leading nonnegative integer entry marker unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "let_op_Op_Const"]
theorem letOp_opConst (trace : BackendCommon.Tra) (n : Nat) (xs : List ClosLang.Exp) :
    ClosLetop.compileList (.op trace (.intOp (.const (Int.ofNat n))) [] :: xs) =
      .op trace (.intOp (.const (Int.ofNat n))) [] :: ClosLetop.compileList xs := by
  rfl

end Flapjack.Compiler.Backend.ClosToBvl
