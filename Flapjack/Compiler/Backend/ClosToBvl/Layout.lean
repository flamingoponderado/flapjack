import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Misc.ListEl

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

/-- Build a recursive closure and install it in the environment. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "recc_Let_def"]
def reccLet (n numArgs i : Nat) : Bvl.Exp :=
  .let [mkElemAt (.var 0) 2]
    (.let [.op (.blockOp (.cons 30)) [.var 0, mkConst (numArgs - 1), mkLabel n]]
      (.let [.op (.memOp .update) [.var 0, mkConst i, .var 1]] (.var 1)))

/-- Source-shaped recursive closure layout. HOL leaves `HD []` unspecified;
the executed checked builder agrees when enough arities are supplied, as
proved in `Proofs/Total.lean`. Full carrier correspondence remains under review. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "recc_Lets_def"]
noncomputable def reccLetsHOL (n : Nat) (args : List Nat) : Nat → Bvl.Exp → Bvl.Exp
  | 0, body => body
  | k + 1, body =>
      .let [reccLet (n + 2 * k) (Flapjack.holHd args) k]
        (reccLetsHOL n args.tail k body)

/-- Build the first recursive closure, whose environment is already in scope. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "recc_Let0_def"]
def reccLet0 (n numArgs i : Nat) : Bvl.Exp :=
  .let [.op (.blockOp (.cons 30)) [.var 0, mkConst (numArgs - 1), mkLabel n]]
    (.let [.op (.memOp .update) [.var 0, mkConst i, .var 1]] (.var 1))

/-- Source-shaped initial recursive closure layout, including HOL's
unspecified empty-list head. The executable checked builder is related for
the nonempty groups supplied by closure compilation. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "build_recc_lets_def"]
noncomputable def buildReccLetsHOL (args vs : List Nat) (n len : Nat) (body : Bvl.Exp) : Bvl.Exp :=
  .let [.let [.op (.memOp .ref) (((args.map fun _ => mkConst 0) ++ (vs.map Bvl.Exp.var)).reverse)]
    (reccLet0 (n + 2 * (len - 1)) (Flapjack.holHd args.reverse) (len - 1))]
    (reccLetsHOL n args.reverse.tail (len - 1) body)

/-- Flapjack's checked form of the recursive-closure builder. It reports a
short argument list instead of selecting HOL's unspecified `HD []`. -/
def reccLets? (n : Nat) : List Nat → Nat → Bvl.Exp → Option Bvl.Exp
  | _, 0, rest => some rest
  | [], _ + 1, _ => none
  | a :: args, k + 1, rest => do
      let body ← reccLets? n args k rest
      pure (.let [reccLet (n + 2 * k) a k] body)

/-- Checked construction of a recursive closure group. A missing arity is
reported explicitly because the source uses unspecified `HD []` there. -/
def buildReccLets? (nargs vs : List Nat) (n1 fnsLen : Nat) (body : Bvl.Exp) : Option Bvl.Exp := do
  let last :: remaining := nargs.reverse | none
  let rest ← reccLets? n1 remaining (fnsLen - 1) body
  pure (.let [.let [.op (.memOp .ref) (((nargs.map fun _ => mkConst 0) ++
      (vs.map Bvl.Exp.var)).reverse)]
      (reccLet0 (n1 + 2 * (fnsLen - 1)) last (fnsLen - 1))] rest)

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
