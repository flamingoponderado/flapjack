module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.FreeVars

@[expose] public section

/-! Free-variable membership across appended expression lists. -/
namespace Flapjack.Compiler.Backend.ClosProps

/-- A free variable occurs in an append exactly when it occurs in either list. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "fv_append"]
theorem freeVars_append (ys : List ClosLang.Exp) (v : Nat) (xs : List ClosLang.Exp) :
    freeVars v (xs ++ ys) ↔ freeVars v xs ∨ freeVars v ys := by
  induction xs with
  | nil => simp [freeVars]
  | cons x xs ih => simp [freeVars, ih, or_assoc]

end Flapjack.Compiler.Backend.ClosProps
