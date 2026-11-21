module

public import Flapjack.Compiler.Backend.DataLang.Syntax
public import Flapjack.HolRef

@[expose] public section

/-! Operation predicates used by the BVI-to-data lowering, in their original
case-split forms. -/
namespace Flapjack.Compiler.Backend.BviToData
open ClosLang

/-- The operation-space reset test in its original case-split form. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "op_space_reset_pmatch"]
theorem op_space_reset_pmatch (op : Op) :
    DataLang.opSpaceReset op = (match op with
      | .intOp .add => true
      | .intOp .sub => true
      | .intOp .mult => true
      | .intOp .div => true
      | .intOp .mod => true
      | .intOp .less => true
      | .intOp .lessEq => true
      | .intOp .greater => true
      | .intOp .greaterEq => true
      | .blockOp .equal => true
      | .blockOp .listAppend => true
      | .blockOp (.fromList _) => true
      | .blockOp (.consExtend _) => true
      | .memOp .refArray => true
      | .memOp (.refByte _) => true
      | .memOp (.copyByte new_flag) => new_flag
      | .memOp .configGC => true
      | .ffi _ => true
      | _ => false) := by
  cases op with
  | intOp i =>
    cases i
    all_goals rfl
  | blockOp b =>
    cases b
    all_goals rfl
  | memOp m =>
    cases m
    all_goals rfl
  | label n => rfl
  | ffi name => rfl
  | wordOp w => rfl
  | globOp g => rfl
  | install => rfl
  | thunkOp t => rfl

set_option linter.unusedVariables false in
/-- The live-name requirement in its original fully enumerated case form. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "op_requires_names_eqn"]
theorem op_requires_names_eqn (op : Op) :
    DataLang.opRequiresNames op =
      (DataLang.opSpaceReset op || (match op with
        | .label _ => false
        | .ffi _ => true
        | .intOp _ => false
        | .wordOp _ => false
        | .blockOp _ => false
        | .globOp _ => false
        | .memOp .ref => false
        | .memOp .update => false
        | .memOp .el => false
        | .memOp .length => false
        | .memOp .lengthByte => false
        | .memOp (.refByte _) => false
        | .memOp .refArray => false
        | .memOp .derefByte => false
        | .memOp .updateByte => false
        | .memOp .concatByteVec => false
        | .memOp (.copyByte new_flag) => true
        | .memOp .fromListByte => false
        | .memOp .toListByte => false
        | .memOp .lengthByteVec => false
        | .memOp .derefByteVec => false
        | .memOp (.stringCmp _ _) => true
        | .memOp .xorByte => true
        | .memOp .boundsCheckArray => false
        | .memOp (.boundsCheckByte _) => false
        | .memOp (.mutCons _ _) => false
        | .memOp .updateCons => false
        | .memOp .finaliseCons => false
        | .memOp .configGC => false
        | .install => true
        | .thunkOp _ => false)) := by
  cases op with
  | intOp i => rfl
  | blockOp b => rfl
  | memOp m =>
    cases m
    all_goals rfl
  | label n => rfl
  | ffi name => rfl
  | wordOp w => rfl
  | globOp g => rfl
  | install => rfl
  | thunkOp t => rfl

set_option linter.unusedVariables false in
/-- The same requirement with HOL's `pmatch` rows; the eliminated form is the
fully enumerated `op_requires_names_eqn`. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "op_requires_names_pmatch"]
theorem op_requires_names_pmatch (op : Op) :
    DataLang.opRequiresNames op =
      (DataLang.opSpaceReset op || (match op with
        | .ffi _ => true
        | .install => true
        | .memOp (.copyByte new_flag) => true
        | .memOp .xorByte => true
        | .memOp (.stringCmp _ _) => true
        | _ => false)) := by
  cases op with
  | intOp i => rfl
  | blockOp b => rfl
  | memOp m =>
    cases m
    all_goals rfl
  | label n => rfl
  | ffi name => rfl
  | wordOp w => rfl
  | globOp g => rfl
  | install => rfl
  | thunkOp t => rfl

end Flapjack.Compiler.Backend.BviToData
