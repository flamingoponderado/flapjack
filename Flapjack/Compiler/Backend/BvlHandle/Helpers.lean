import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.HolRef

/-! Source-shaped helpers for BVL handler compilation. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl

mutual
/-- Whether an expression can raise according to the original handler pass. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "can_raise_def"]
def canRaise : Exp → Bool
  | .var _ => false
  | .ifThenElse x y z => canRaise x || canRaise y || canRaise z
  | .let xs body => canRaise body || canRaiseList xs
  | .handle _ handler => canRaise handler
  | .raise _ | .force _ _ | .call _ _ _ => true
  | .op (.thunkOp .forceThunk) _ => true
  | .op _ xs => canRaiseList xs
  | .tick body => canRaise body
termination_by expression => sizeOf expression

/-- Whether any expression in a list can raise. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "can_raise_def"]
def canRaiseList : List Exp → Bool
  | [] => false
  | e :: es => canRaise e || canRaiseList es
termination_by expressions => sizeOf expressions
end

/-- Recognize a raise whose argument cannot itself raise. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "dest_handle_Raise_def"]
def destHandleRaise (expression : Exp) : Option Exp :=
  match expression with
  | .raise body => if canRaise body then none else some body
  | _ => none

/-- Recognize a let whose bindings cannot raise. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "dest_handle_Let_def"]
def destHandleLet (expression : Exp) : Option (List Exp × Exp) :=
  match expression with
  | .let xs body => if canRaiseList xs then none else some (xs, body)
  | _ => none

/-- Recognize an if with a safe condition and exactly one raising branch. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "dest_handle_If_def"]
def destHandleIf (expression : Exp) : Option ((Exp × Exp × Exp) ⊕ (Exp × Exp × Exp)) :=
  match expression with
  | .ifThenElse condition yes no =>
    if canRaise condition then none
    else if canRaise yes then
      if canRaise no then none else some (.inl (condition, yes, no))
    else if canRaise no then
      if canRaise yes then none else some (.inr (condition, yes, no))
    else none
  | _ => none

mutual
/-- Shift free variables at or above the binder depth. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "handle_adj_vars_def"]
def handleAdjVars (depth shift : Nat) : Exp → Exp
  | .var n => .var (if n < depth then n else n + shift)
  | .ifThenElse x y z => .ifThenElse (handleAdjVars depth shift x)
      (handleAdjVars depth shift y) (handleAdjVars depth shift z)
  | .let xs body => .let (handleAdjVarsList depth shift xs)
      (handleAdjVars (depth + xs.length) shift body)
  | .handle body handler => .handle (handleAdjVars depth shift body)
      (handleAdjVars (depth + 1) shift handler)
  | .raise body => .raise (handleAdjVars depth shift body)
  | .op op xs => .op op (handleAdjVarsList depth shift xs)
  | .tick body => .tick (handleAdjVars depth shift body)
  | .force location n => .force location (if n < depth then n else n + shift)
  | .call ticks dest xs => .call ticks dest (handleAdjVarsList depth shift xs)
termination_by expression => sizeOf expression

/-- Shift free variables in an expression list. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "handle_adj_vars_def"]
def handleAdjVarsList (depth shift : Nat) : List Exp → List Exp
  | [] => []
  | e :: es => handleAdjVars depth shift e :: handleAdjVarsList depth shift es
termination_by expressions => sizeOf expressions
end

mutual
/-- Original weighted size used to justify handler simplification termination. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "handle_size_def"]
def handleSize : Exp → Nat
  | .var _ | .force _ _ => 1
  | .ifThenElse x y z => 1 + handleSize x + handleSize y + handleSize z
  | .let xs body => 1 + handleSize body + handleSizeList xs
  | .handle body handler => 1 + 5 * (handleSize body + handleSize handler)
  | .raise body | .tick body => 1 + handleSize body
  | .op _ xs | .call _ _ xs => 1 + handleSizeList xs
termination_by expression => sizeOf expression

/-- Original weighted list size. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "handle_size_def"]
def handleSizeList : List Exp → Nat
  | [] => 1
  | e :: es => 1 + handleSize e + handleSizeList es
termination_by expressions => sizeOf expressions
end

end Flapjack.Compiler.Backend.BvlHandle
