import Flapjack.Compiler.Backend.Semantics.BvlSem.Value
import Flapjack.Compiler.Backend.BvlToBvi.Config
/-! Value relocation used by the BVL-to-BVI state relation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BackendCommon

mutual
/-- Translate references and code labels while retaining the BVL value shape. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "adjust_bv_def"]
def adjustBv (relocate : Nat → Nat) : Value → Value
  | .number n => .number n
  | .word64 w => .word64 w
  | .refPtr mutableRef address => .refPtr mutableRef (relocate address)
  | .codePtr label => .codePtr (bvlNumStubs + bvlToBviNamespaces * label)
  | .block tag values => .block tag (adjustValues relocate values)
termination_by v => sizeOf v

/-- Flapjack helper for the source value mapping on a block’s children. -/
def adjustValues (relocate : Nat → Nat) : List Value → List Value
  | [] => []
  | value :: rest => adjustBv relocate value :: adjustValues relocate rest
termination_by values => sizeOf values
end

/-- The local list recursion is exactly the source MAP of adjusted values. -/
theorem adjustValues_eq_map (relocate : Nat → Nat) (values : List Value) :
    adjustValues relocate values = values.map (adjustBv relocate) := by
  induction values with
  | nil => simp [adjustValues]
  | cons value rest ih => simpa [adjustValues] using congrArg (List.cons (adjustBv relocate value)) ih

/-- The block equation exposes the original MAP formulation. -/
theorem adjustBv_block (relocate : Nat → Nat) (tag : Nat) (values : List Value) :
    adjustBv relocate (.block tag values) = .block tag (values.map (adjustBv relocate)) := by
  simp [adjustBv, adjustValues_eq_map]

/-- The original value transformation fixes the unit value. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "adjust_bv_Unit"]
theorem adjustBv_unit (relocate : Nat → Nat) : adjustBv relocate unitValue = unitValue := by
  simp [unitValue, adjustBv, adjustValues]

/-- The original value transformation fixes both Boolean values. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "adjust_bv_Boolv"]
theorem adjustBv_bool (relocate : Nat → Nat) (b : Bool) : adjustBv relocate (boolValue b) = boolValue b := by
  cases b <;> simp [boolValue, adjustBv, adjustValues]
end Flapjack.Compiler.Backend.BvlToBvi.Proofs
