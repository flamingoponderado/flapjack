module

public import Flapjack.Compiler.Backend.Semantics.BvlSem.Value

@[expose] public section

/-! Runtime values of the data-language semantics. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack.Compiler.Backend.BackendCommon

/-- Data-language values retain the allocation timestamp on blocks. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "v"]
inductive Value where
  | number : Int → Value
  | word64 : BitVec 64 → Value
  | block : Nat → Nat → List Value → Value
  | codePtr : Nat → Value
  | refPtr : Bool → Nat → Value
  deriving BEq, Repr

/-- The source Boolean block, whose timestamp is zero. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "Boolv_def"]
def boolValue (b : Bool) : Value := .block 0 (boolToTag b) []

/-- The source unit block, whose timestamp is zero. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "Unit_def"]
def unitValue : Value := .block 0 0 []

/-- Decode nil and cons blocks, ignoring their timestamps. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "v_to_list_def"]
def valueToList : Value → Option (List Value)
  | .block _ tag [] => if tag = nilTag then some [] else none
  | .block _ tag [head, tail] =>
      if tag = consTag then (valueToList tail).map (head :: ·) else none
  | _ => none
termination_by value => sizeOf value

end Flapjack.Compiler.Backend.DataSem
