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

/-- The `dest_Const` matcher written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_Const_pmatch"]
theorem destConst_pmatch (x : Op) :
    destConst x = match x with | .intOp (.const i) => some i | _ => none := by
  cases x
  all_goals simp [destConst]

/-- The `dest_Constant` matcher written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_Constant_pmatch"]
theorem destConstant_pmatch (x : Op) :
    destConstant x = match x with
      | .blockOp (.constant (.constStr c)) => some (.str c)
      | .blockOp (.constant (.constInt i)) => some (.int i)
      | .blockOp (.constant (.constWord64 w)) => some (.w64 w)
      | _ => none := by
  cases x
  all_goals simp [destConstant]

/-- The `dest_Cons` matcher written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_Cons_pmatch"]
theorem destCons_pmatch (x : Op) :
    destCons x = match x with | .blockOp (.cons i) => some i | _ => none := by
  cases x
  all_goals simp [destCons]

/-- The `dest_ElemAt` matcher written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_ElemAt_pmatch"]
theorem destElemAt_pmatch (x : Op) :
    destElemAt x = match x with | .blockOp (.elemAt i) => some i | _ => none := by
  cases x
  all_goals simp [destElemAt]

/-- The `dest_TagEq` matcher written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_TagEq_pmatch"]
theorem destTagEq_pmatch (x : Op) :
    destTagEq x = match x with | .blockOp (.tagEq i) => some i | _ => none := by
  cases x
  all_goals simp [destTagEq]

/-- The `dest_LenEq` matcher written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_LenEq_pmatch"]
theorem destLenEq_pmatch (x : Op) :
    destLenEq x = match x with | .blockOp (.lenEq i) => some i | _ => none := by
  cases x
  all_goals simp [destLenEq]

/-- The `dest_TagLenEq` matcher written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_TagLenEq_pmatch"]
theorem destTagLenEq_pmatch (x : Op) :
    destTagLenEq x = match x with | .blockOp (.tagLenEq i j) => some (i, j) | _ => none := by
  cases x
  all_goals simp [destTagLenEq]

/-- The `dest_Op` matcher written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "dest_Op_pmatch"]
theorem destOp_pmatch {α : Type} (f : Op → Option α) (x : Exp) :
    destOp f x = match x with
      | .op _ op xs => match f op with | none => none | some i => some (i, xs)
      | _ => none := by
  cases x with
  | op _ op xs =>
    cases h : f op with
    | none => simp [destOp, h]
    | some i => simp [destOp, h]
  | _ => simp [destOp]

end Flapjack.Compiler.Backend.ClosOp
