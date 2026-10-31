import Flapjack.Compiler.Backend.BviTailrec.Proofs.ScanTotal
import Flapjack.Compiler.Backend.BviTailrec.Proofs.TermCorrespondence
import Flapjack.Compiler.Backend.BviTailrec.Proofs.HasRecCorrespondence

/-! Correspondence between source-shaped and executed tail-recursion scans. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

/-- Every recognized accumulator operator round-trips to its source BVI
operation. -/
theorem toOp_fromOp (op : ClosLang.Op) (recognized : fromOp op ≠ .noop) : toOp (fromOp op) = op := by
  cases op <;> try (simp_all [fromOp, toOp])
  case intOp operation => cases operation <;> simp_all
  case blockOp operation => cases operation <;> simp_all

/-- Classifying an accumulator operation after conversion recovers it. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "from_op_to_op"]
theorem fromOp_toOp (assoc : AssocOp) : fromOp (toOp assoc) = assoc := by
  cases assoc <;> rfl

/-- Candidate analysis agrees with the source check on each operation
recognized by `fromOp`. -/
theorem checkOpFuel_eq_recognized (fuel : Nat) (ctx : List ValueType) (op : ClosLang.Op)
    (loc : Nat) (args : List Exp) (recognized : fromOp op ≠ .noop) :
    checkOpFuel fuel ctx (fromOp op) loc args = some (checkOp ctx (fromOp op) loc (.op op args)) := by
  have opEq := toOp_fromOp op recognized
  simpa only [opEq] using checkOpFuel_eq fuel ctx (fromOp op) loc args recognized

/-- The operation branch of the executed scan agrees with the source scan
whenever it returns. -/
theorem scanFuel_op_eq (fuel : Nat) (ctx : List ValueType) (loc : Nat)
    (op : ClosLang.Op) (args : List Exp)
    (result : List ValueType × ValueType × Bool × Option AssocOp)
    (run : scanFuel (fuel + 1) ctx loc (.op op args) = some result) :
    result = scanSing ctx loc (.op op args) := by
  have same : scanFuel (fuel + 1) ctx loc (.op op args) = some (scanSing ctx loc (.op op args)) := by
    rw [scanFuel.eq_def, scanSing.eq_def]
    dsimp only
    cases assoc : fromOp op with
    | noop =>
      simp only [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx]
      cases args with
      | nil => cases op <;> simp_all [apply_ite] <;> split <;> simp_all
      | cons x xs => cases xs with
        | nil => simp_all [apply_ite]
        | cons y ys => cases ys <;> simp_all [apply_ite]
    | plus | times | append =>
      have recognized : fromOp op ≠ .noop := by rw [assoc]; decide
      have checked := checkOpFuel_eq_recognized fuel ctx op loc args recognized
      rw [assoc] at checked
      simp only [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx,
        checked, termBounded_eq, bind, Option.bind, pure]
      cases check : checkOp ctx _ loc (.op op args) <;> cases termResult : term ctx _ (.op op args) <;>
        cases args with
        | nil => simp_all
        | cons x xs => cases xs with
          | nil => simp_all
          | cons y ys => cases ys <;> simp_all
  rw [same] at run
  exact (Option.some.inj run).symm

end Flapjack.Compiler.Backend.BviTailrec
