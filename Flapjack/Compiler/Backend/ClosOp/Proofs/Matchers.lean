import Flapjack.Compiler.Backend.ClosOp

/-! Agreement of the reviewed source matchers with the former executable
patterns. These are Flapjack preservation facts, not separate HOL theorems. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

/-- The source integer-expression matcher preserves the former pattern. -/
theorem destOpConst_eq_previous (e : Exp) :
    destOpNil destConst e = match e with
      | .op _ (.intOp (.const i)) [] => some i
      | _ => none := by
  cases e <;> try rfl
  case op t op xs =>
    cases op <;> try rfl
    case intOp i => cases i <;> cases xs <;> rfl

/-- The source constructor-expression matcher preserves the former pattern. -/
theorem destOpCons_eq_previous (e : Exp) :
    cons e = match e with
      | .op _ (.blockOp (.cons tag)) xs => some (tag, xs)
      | _ => none := by
  cases e <;> try rfl
  case op t op xs =>
    cases op <;> try rfl
    case blockOp op => cases op <;> rfl

/-- The source nullary-constructor matcher preserves the former pattern. -/
theorem destOpConsNil_eq_previous (e : Exp) :
    destOpNil destCons e = match e with
      | .op _ (.blockOp (.cons tag)) [] => some tag
      | _ => none := by
  cases e <;> try rfl
  case op t op xs =>
    cases op <;> try rfl
    case blockOp op => cases op <;> cases xs <;> rfl

/-- The source constant-expression matcher preserves the former pattern. -/
theorem destOpConstant_eq_previous (e : Exp) :
    destOpNil destConstant e = match e with
      | .op _ (.blockOp (.constant (.constInt i))) [] => some (.int i)
      | .op _ (.blockOp (.constant (.constStr s))) [] => some (.str s)
      | .op _ (.blockOp (.constant (.constWord64 w))) [] => some (.w64 w)
      | _ => none := by
  cases e <;> try rfl
  case op t op xs =>
    cases op <;> try rfl
    case blockOp op =>
      cases op <;> try rfl
      case constant value => cases value <;> cases xs <;> rfl

end Flapjack.Compiler.Backend.ClosOp
