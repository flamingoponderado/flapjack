module

public import Flapjack.Compiler.Backend.Bvi.Syntax

@[expose] public section

/-! Helpers for the BVI let-propagation pass. -/
namespace Flapjack.Compiler.Backend.BviLet

/-- Exact port of HOL `bvi_let$extract_def` (`bvi_letScript.sml`):
`extract (Var n) ys = n + LENGTH ys + 1` and `0` for every other expression
constructor.  The typed capture (`extract_def_typed` in
`scripts/hol-probes/bvi_let_helpers_probe.out`) keeps the displaced list's
element type generic (`ys :α list`), so the twin binds `{α : Type}`; the
expression argument is HOL's fixed BVI `exp` type, matching `Bvi.Exp`. -/
@[hol "cakeml/compiler/backend/bvi_letScript.sml" "extract_def"]
def extract {α : Type} (e : Bvi.Exp) (ys : List α) : Nat :=
  match e with | .var n => n + ys.length + 1 | _ => 0

/-- Build the displacement environment from right to left. -/
@[hol "cakeml/compiler/backend/bvi_letScript.sml" "extract_list_def"]
def extractList : List Bvi.Exp → List Nat
  | [] => []
  | x :: xs => extract x xs :: extractList xs

/-- Replace propagated variable expressions by the source's zero constant. -/
@[hol "cakeml/compiler/backend/bvi_letScript.sml" "delete_var_def"]
def deleteVar : Bvi.Exp → Bvi.Exp
  | .var _ => .op (.intOp (.const 0)) []
  | e => e

end Flapjack.Compiler.Backend.BviLet
