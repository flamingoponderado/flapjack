import Flapjack.Compiler.Backend.DataSpace.Requirements

/-! Lower a BVI operation into a data-language assignment. -/
namespace Flapjack.Compiler.Backend.BviToData

/-- Source-shaped construction of a live-name set, using HOL's right fold. -/
def namesOfList : List Nat → NumSet
  | [] => .ln
  | n :: ns => sptInsert n () (namesOfList ns)

/-- Emit the source assignment, including required live names, allocation
space and reversed operands for greater-than comparisons. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "iAssign_def"]
def iAssign (n : Nat) (op : ClosLang.Op) (vs live env : List Nat) : DataLang.Prog :=
  let names := namesOfList (vs ++ live ++ env)
  if DataLang.opRequiresNames op then
    match op with
    | .intOp .greater => .assign n (.intOp .less) vs.reverse (some names)
    | .intOp .greaterEq => .assign n (.intOp .lessEq) vs.reverse (some names)
    | _ => .assign n op vs (some names)
  else
    let k := DataSpace.opSpaceReq op vs.length
    if k = 0 then
      match op with
      | .wordOp (.wordTest .w8 (.compare .gt)) =>
          .assign n (.wordOp (.wordTest .w8 (.compare .lt))) vs.reverse none
      | .wordOp (.wordTest .w8 (.compare .geq)) =>
          .assign n (.wordOp (.wordTest .w8 (.compare .leq))) vs.reverse none
      | _ => .assign n op vs none
    else .seq (.makeSpace k names) (.assign n op vs none)

end Flapjack.Compiler.Backend.BviToData
