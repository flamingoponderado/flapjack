module

public import Flapjack.Compiler.Backend.ClosLang.Syntax

@[expose] public section

/-! Source matchers and constructors used by closure smart operations. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_Const_def"]
def destConst : Op → Option Int
  | .intOp (.const i) => some i
  | _ => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_Constant_def"]
def destConstant : Op → Option ConstPart
  | .blockOp (.constant (.constStr s)) => some (.str s)
  | .blockOp (.constant (.constInt i)) => some (.int i)
  | .blockOp (.constant (.constWord64 w)) => some (.w64 w)
  | _ => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_Cons_def"]
def destCons : Op → Option Nat
  | .blockOp (.cons tag) => some tag
  | _ => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_ElemAt_def"]
def destElemAt : Op → Option Nat
  | .blockOp (.elemAt i) => some i
  | _ => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_TagEq_def"]
def destTagEq : Op → Option Nat
  | .blockOp (.tagEq tag) => some tag
  | _ => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_LenEq_def"]
def destLenEq : Op → Option Nat
  | .blockOp (.lenEq len) => some len
  | _ => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_TagLenEq_def"]
def destTagLenEq : Op → Option (Nat × Nat)
  | .blockOp (.tagLenEq tag len) => some (tag, len)
  | _ => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_Op_def"]
def destOp {α : Type} (f : Op → Option α) : Exp → Option (α × List Exp)
  | .op _ op xs => (f op).map (fun value => (value, xs))
  | _ => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_Op_Nil_def"]
def destOpNil {α : Type} (f : Op → Option α) (e : Exp) : Option α := do
  let (value, args) ← destOp f e
  if args.isEmpty then some value else none

/-- Match constructor operations and retain their arguments. -/
def cons : Exp → Option (Nat × List Exp) := destOp destCons

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_Op_Consts_def"]
def destOpConsts (x y : Exp) : Option (Int × Int) := do
  let i ← destOpNil destConst x
  let j ← destOpNil destConst y
  some (i, j)

@[hol "cakeml/compiler/backend/clos_opScript.sml" "MakeBool_def"]
def mkBool (b : Bool) : Exp := .op .none (.blockOp (.cons (if b then 1 else 0))) []

@[hol "cakeml/compiler/backend/clos_opScript.sml" "MakeInt_def"]
def mkInt (i : Int) : Exp := .op .none (.intOp (.const i)) []

end Flapjack.Compiler.Backend.ClosOp
