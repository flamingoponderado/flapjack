import Flapjack.Compiler.Backend.ClosLetop.Source
import Flapjack.Compiler.Backend.Semantics.ClosProps.AppCallDests

/-! Call-destination properties of let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang ClosProps

/-- A recognized variable list has no application or call destinations. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "var_list_app_call_dests"]
theorem varList_appCallDests {α : Type} (n : Nat) (xs : List Exp) (ys : List α)
    (selection : Option Bool) (h : varList n xs ys = true) : appCallDests selection xs = ∅ := by
  induction xs generalizing n ys with
  | nil => simp [appCallDests]
  | cons x xs ih =>
    cases ys with
    | nil => simp [varList] at h
    | cons y ys =>
      cases x <;> simp [varList] at h
      case var trace index =>
        rw [show Exp.var trace index :: xs = [Exp.var trace index] ++ xs from rfl,
          appCallDests_append]
        simp [appCallDests, ih (n + 1) ys h.2]

end Flapjack.Compiler.Backend.ClosLetop
