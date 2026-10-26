import Flapjack.Compiler.Backend.Bvl.Syntax

/-! Closure-to-BVL code-layout and small instruction constructors. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Build a BVL integer constant. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "mk_const_def"]
def mkConst (n : Nat) : Bvl.Exp := .op (.intOp (.const (Int.ofNat n))) []

/-- Build a BVL code label. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "mk_label_def"]
def mkLabel (n : Nat) : Bvl.Exp := .op (.label n) []

/-- Build an element access, preserving the source index/array operand order. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "mk_el_def"]
def mkEl (b i : Bvl.Exp) : Bvl.Exp := .op (.memOp .el) [i, b]

/-- The BVL `mk_elem_at` overload, used by closure-environment extraction. -/
private def mkElemAt (b : Bvl.Exp) (i : Nat) : Bvl.Exp := .op (.blockOp (.elemAt i)) [b]

/-- Read the free variables stored after the two closure metadata fields. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "free_let_def"]
def freeLet (cl : Bvl.Exp) (n : Nat) : List Bvl.Exp :=
  (List.range n).map (fun i => mkElemAt cl (i + 2))

/-- Wrap a recursively defined function body with its argument and environment
extractions. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "code_for_recc_case_def"]
def codeForReccCase (n numArgs : Nat) (body : Bvl.Exp) : Nat × Bvl.Exp :=
  (numArgs + 1, .let [mkElemAt (.var numArgs) 2]
    (.let ((List.range numArgs).map (fun a => .var (a + 1)) ++
      (List.range n).map (fun i => mkElemAt (.var 0) i)) body))

/-- Assign successive even locations to recursive-function bodies, prepending
each generated entry to the auxiliary table. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "build_aux_def"]
def buildAux (i : Nat) : List (Nat × Bvl.Exp) → List (Nat × Nat × Bvl.Exp) →
    Nat × List (Nat × Nat × Bvl.Exp)
  | [], aux => (i, aux)
  | (arity, body) :: xs, aux => buildAux (i + 2) xs ((i, arity, body) :: aux)

/-- Count generic, partial-application, initialization and force stubs. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "num_stubs_def"]
def numStubs (maxApp : Nat) : Nat := maxApp + maxApp * (maxApp - 1) / 2 + 1 + 1

/-- Location of a generic-application stub. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "generic_app_fn_location_def"]
def genericAppFnLocation (n : Nat) : Nat := n

/-- Location of a partial-application stub. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "partial_app_fn_location_def"]
def partialAppFnLocation (maxApp total previous : Nat) : Nat :=
  maxApp + total * (total - 1) / 2 + previous

/-- Emit the BVL expression for a computed stub location. HOL infers the unused
first argument polymorphically; the separate surrounding code supplies its
own `max_app` offset. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "partial_app_fn_location_code_def"]
def partialAppFnLocationCode {α : Type} (_maxApp : α) (total previous : Bvl.Exp) : Bvl.Exp :=
  .let [total] (.op (.intOp .add) [previous,
    .op (.intOp .div) [mkConst 2,
      .op (.intOp .mult) [.var 0, .op (.intOp .sub) [mkConst 1, .var 0]]]])

/-- Emit the direct-call or generic-application branch for a closure. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "mk_cl_call_def"]
def mkClCall (cl : Bvl.Exp) (args : List Bvl.Exp) : Bvl.Exp :=
  let arity := args.length - 1
  .ifThenElse (.op (.blockOp (.equalConst (.int (Int.ofNat arity)))) [mkElemAt cl 1])
    (.call arity none (args ++ [cl, mkElemAt cl 0]))
    (.call 0 (some (genericAppFnLocation arity)) (args ++ [cl]))

/-- Emit the function that completes a partial closure application. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "generate_partial_app_closure_fn_def"]
def generatePartialAppClosureFn (totalArgs prevArgs : Nat) : Bvl.Exp :=
  .let [mkElemAt (.var (totalArgs - prevArgs)) 2]
    (.call 0 none
      ((List.range (totalArgs - prevArgs)).map (fun arg => .var (arg + 1)) ++
       (List.range (prevArgs + 1)).map (fun arg =>
         mkElemAt (.var (totalArgs - prevArgs + 1)) (arg + 3)) ++
       [.var 0, mkElemAt (.var 0) 0]))

/-- Chain top-level closure expressions through successive zero-argument calls. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "chain_exps_def"]
def chainExps (i : Nat) : List ClosLang.Exp → List (Nat × Nat × ClosLang.Exp)
  | [] => [(i, 0, .op .none (.intOp (.const 0)) [])]
  | [e] => [(i, 0, e)]
  | e :: e2 :: es =>
      (i, 0, .let .none [e] (.call .none 0 (i + 1) [])) :: chainExps (i + 1) (e2 :: es)

end Flapjack.Compiler.Backend.ClosToBvl
