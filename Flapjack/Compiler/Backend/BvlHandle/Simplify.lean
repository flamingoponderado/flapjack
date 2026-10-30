import Flapjack.Compiler.Backend.BvlHandle.Proofs.Helpers

/-! Total source-shaped BVL handler simplification. The executed compiler
still uses `simplifyBounded`; its correspondence with these definitions is
not yet proved. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl
open Flapjack.Compiler.Backend.BvlHandle.Proofs

mutual
/-- Simplify handlers in one expression. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "handle_simp_def"]
def handleSimp : Exp → Exp
  | .handle body handler => makeHandle body handler 0
  | .var n => .var n
  | .ifThenElse x y z => .ifThenElse (handleSimp x) (handleSimp y) (handleSimp z)
  | .let xs body => .let (handleSimpList xs) (handleSimp body)
  | .raise body => .raise (handleSimp body)
  | .op op xs => .op op (handleSimpList xs)
  | .tick body => .tick (handleSimp body)
  | .force location index => .force location index
  | .call ticks dest xs => .call ticks dest (handleSimpList xs)
termination_by expression => handleSize expression
decreasing_by all_goals simp_wf <;> simp_all [handleSize] <;> omega

/-- Simplify handlers in an expression list. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "handle_simp_def"]
def handleSimpList : List Exp → List Exp
  | [] => []
  | e :: es => handleSimp e :: handleSimpList es
termination_by expressions => handleSizeList expressions
decreasing_by all_goals simp_wf <;> simp_all [handleSizeList] <;> omega

/-- Push a handler through source-recognized safe expressions. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "handle_simp_def"]
def makeHandle (body handler : Exp) (depth : Nat) : Exp :=
  match body with
  | .raise value =>
    if canRaise value then
      .handle (handleSimp (.raise value)) (handleAdjVars 1 depth (handleSimp handler))
    else .let [value] (handleAdjVars 1 depth (handleSimp handler))
  | .let xs next =>
    if canRaiseList xs then
      .handle (handleSimp (.let xs next)) (handleAdjVars 1 depth (handleSimp handler))
    else .let (handleSimpList xs) (makeHandle next handler (depth + xs.length))
  | .ifThenElse condition yes no =>
    if canRaise condition then
      .handle (handleSimp (.ifThenElse condition yes no)) (handleAdjVars 1 depth (handleSimp handler))
    else if canRaise yes then
      if canRaise no then
        .handle (handleSimp (.ifThenElse condition yes no)) (handleAdjVars 1 depth (handleSimp handler))
      else .ifThenElse (handleSimp condition) (makeHandle yes handler depth) (handleSimp no)
    else if canRaise no then
      .ifThenElse (handleSimp condition) (handleSimp yes) (makeHandle no handler depth)
    else .handle (handleSimp (.ifThenElse condition yes no)) (handleAdjVars 1 depth (handleSimp handler))
  | other => .handle (handleSimp other) (handleAdjVars 1 depth (handleSimp handler))
termination_by handleSize body + handleSize handler
decreasing_by
  all_goals simp_wf
  all_goals try simp_all [handleSize]
  all_goals have h := handleSize_nonzero handler
  all_goals try omega
  all_goals exact handleSize_nonzero _
end

end Flapjack.Compiler.Backend.BvlHandle
