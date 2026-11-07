import Flapjack.Compiler.Backend.ClosInterp.Interpreter

/-! Interpreter insertion for incremental closure compilation. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open ClosLang

/-- Test whether an operator is supported at the given arity. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "can_interpret_op_def"]
def canInterpretOp (op : Op) (len : Nat) : Bool :=
  match op with
  | .blockOp (.cons tag) => len == 0 || tag < 3
  | .intOp (.const _) | .globOp (.global _) | .blockOp (.constant _) => len == 0
  | _ => false

mutual
/-- Test whether an expression is in the interpreter's supported subset. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "can_interpret_def"]
def canInterpret : Exp → Bool
  | .var _ _ => true
  | .ifThenElse _ a b c => canInterpret a && canInterpret b && canInterpret c
  | .let _ es e => canInterpret e && canInterpretList es
  | .op _ op es => canInterpretOp op es.length && canInterpretList es
  | .raise _ e | .tick _ e => canInterpret e
  | .handle _ a b => canInterpret a && canInterpret b
  | .app _ opt e es => opt.isNone && canInterpret e && canInterpretList es && es.length == 1
  | .fn _ _ _ _ _ | .call _ _ _ _ | .letrec _ _ _ _ _ => false

/-- List clauses of the supported-subset test. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "can_interpret_def"]
def canInterpretList : List Exp → Bool
  | [] => true
  | e :: es => canInterpret e && canInterpretList es
end

/-- Consume size budget for the original operator cases. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "check_size_op_def"]
def checkSizeOp (k : Nat) (op : Op) (len : Nat) : Nat :=
  match op with
  | .blockOp (.cons _) => if len = 0 then k else k - 1
  | .intOp (.const _) | .globOp (.global _) => k
  | _ => k - 1

mutual
/-- Consume the source's size budget in evaluation order. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "check_size_def"]
def checkSize (k : Nat) : Exp → Nat
  | .var _ _ => k
  | .ifThenElse _ a b c =>
      let k := checkSize k a
      if k = 0 then 0 else
        let k := checkSize k b
        if k = 0 then 0 else checkSize k c
  | .let _ es e =>
      let k := checkSizeList k es
      if k = 0 then 0 else checkSize k e
  | .op _ op es =>
      let k := checkSizeOp k op es.length
      if k = 0 then 0 else checkSizeList k es
  | .raise _ e | .tick _ e => checkSize k e
  | .handle _ a b =>
      let k := checkSize k a
      if k = 0 then 0 else checkSize k b
  | .app _ _ e es =>
      let k := checkSize (k - 1) e
      if k = 0 then 0 else checkSizeList k es
  | .fn _ _ _ _ _ | .call _ _ _ _ | .letrec _ _ _ _ _ => k

/-- List clauses of the size-budget traversal. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "check_size_def"]
def checkSizeList (k : Nat) : List Exp → Nat
  | [] => k
  | e :: es =>
      let k := checkSize k e
      if k = 0 then 0 else checkSizeList k es
end

/-- Original threshold for interpreter replacement. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "nontrivial_size_def"]
def nontrivialSize (e : Exp) : Bool := checkSize 8 e == 0

/-- Convert a supported operator into the interpreter's constant encoding. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "to_constant_op_def"]
def toConstantOp (op : Op) (len : Nat) (cs : Const) : Const :=
  match op with
  | .intOp (.const i) => .constCons 1 [.constInt i]
  | .blockOp (.constant c) => .constCons 1 [c]
  | .globOp (.global n) => .constCons 2 [.constInt (Int.ofNat n)]
  | .blockOp (.cons tag) =>
      if len = 0 then .constCons 1 [.constCons tag []] else .constCons (tag + 5) [cs]
  | _ => .constInt 0

mutual
/-- Encode a closure expression as the interpreter's constant representation. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "to_constant_def"]
def toConstant : Exp → Const
  | .var _ n => .constCons 0 [.constInt (Int.ofNat n)]
  | .app _ _ e [] => .constCons 0 [toConstant e, .constInt 0]
  | .app _ _ e (x :: _) => .constCons 0 [toConstant e, toConstant x]
  | .ifThenElse _ a b c => .constCons 0 [toConstant a, toConstant b, toConstant c]
  | .let _ es e => .constCons 1 [toConstantList es, toConstant e]
  | .op _ op es => toConstantOp op es.length (toConstantList es)
  | .raise _ e => .constCons 3 [toConstant e]
  | .tick _ e => .constCons 4 [toConstant e]
  | .handle _ a b => .constCons 2 [toConstant a, toConstant b]
  | .fn _ _ _ _ _ | .call _ _ _ _ | .letrec _ _ _ _ _ => .constInt 0

/-- Encode the source list representation, including its empty constructor. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "to_constant_def"]
def toConstantList : List Exp → Const
  | [] => .constCons 0 []
  | e :: es => .constCons 0 [toConstant e, toConstantList es]
end

/-- Replace a sufficiently large interpretable expression with an interpreter call. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "opt_interp_def"]
def optInterp (e : Exp) : Option Exp :=
  if canInterpret e && nontrivialSize e then
    let global := Exp.op .none (.globOp (.global 0)) []
    let env := Exp.op .none (.blockOp (.cons 0)) []
    let encoded := Exp.op .none (.blockOp (.constant (toConstant e))) []
    some (.app .none none (.app .none none (.app .none none global [env]) [env]) [encoded])
  else none

/-- Retain the original expression if it is not selected for interpretation. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "opt_interp1_def"]
def optInterp1 (e : Exp) : Exp := (optInterp e).getD e

/-- Apply the source's one-level fallback to a `Let` when the whole expression
is not replaced. Its trace is deliberately reset to `None`, as in HOL. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "insert_interp1_def"]
def insertInterp1 (e : Exp) : Exp :=
  match optInterp e with
  | some e' => e'
  | none => match e with
    | .let _ ys y => .let .none (ys.map optInterp1) y
    | _ => e

/-- Apply incremental interpreter insertion to each top-level expression. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "insert_interp_def"]
def insertInterp (es : List Exp) : List Exp := es.map insertInterp1

end Flapjack.Compiler.Backend.ClosInterp
