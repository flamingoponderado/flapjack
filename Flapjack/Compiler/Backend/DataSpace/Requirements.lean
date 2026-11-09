import Flapjack.Compiler.Backend.DataLang.Syntax

/-! Allocation-space requirements for data-language operations. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack.Basis.Pure.MlString

/-- Number of words needed for an arbitrary-precision natural number. -/
@[hol "cakeml/compiler/backend/data_spaceScript.sml" "num_size_def"]
def numSize (n : Nat) : Nat :=
  if n < 4294967296 then 2 else 1 + numSize (n / 4294967296)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Space required by a flattened constant part. -/
@[hol "cakeml/compiler/backend/data_spaceScript.sml" "part_space_req_def"]
def partSpaceReq : ClosLang.ConstPart → Nat
  | .w64 _ => 3
  | .int i => if i.natAbs < 536870912 then 0 else numSize i.natAbs
  | .str s => s.explode.length / 4 + 2
  | .con _ ns => if ns.isEmpty then 0 else ns.length + 1

/-- Space consumed by an operation with the given operand count. -/
@[hol "cakeml/compiler/backend/data_spaceScript.sml" "op_space_req_def"]
def opSpaceReq : ClosLang.Op → Nat → Nat
  | .memOp .ref, l | .memOp (.mutCons _ _), l | .thunkOp (.allocThunk _), l => l + 1
  | .blockOp (.cons _), l => if l = 0 then 0 else l + 1
  | .blockOp (.build parts), _ => (parts.map partSpaceReq).sum
  | .wordOp (.wordOpw .w64 _), _ | .wordOp (.wordShift .w64 _ _), _
  | .wordOp .wordFromInt, _ | .wordOp .wordToInt, _ | .wordOp (.wordFromWord false), _
  | .wordOp (.fpUop _), _ | .wordOp (.fpBop _), _ | .wordOp (.fpTop _), _ => 3
  | _, _ => 0

end Flapjack.Compiler.Backend.DataSpace
