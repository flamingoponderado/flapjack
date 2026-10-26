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

/-- Chain top-level closure expressions through successive zero-argument calls. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "chain_exps_def"]
def chainExps (i : Nat) : List ClosLang.Exp → List (Nat × Nat × ClosLang.Exp)
  | [] => [(i, 0, .op .none (.intOp (.const 0)) [])]
  | [e] => [(i, 0, e)]
  | e :: e2 :: es =>
      (i, 0, .let .none [e] (.call .none 0 (i + 1) [])) :: chainExps (i + 1) (e2 :: es)

end Flapjack.Compiler.Backend.ClosToBvl
