import Flapjack.Compiler.Backend.Bvi.Syntax

/-! Helpers for the BVI let-propagation pass. -/
namespace Flapjack.Compiler.Backend.BviLet

/-- Compute the displacement for a variable binding; other expressions do
not introduce a propagated variable. -/
@[hol "cakeml/compiler/backend/bvi_letScript.sml" "extract_def"]
def extract (e : Bvi.Exp) (ys : List Bvi.Exp) : Nat :=
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
