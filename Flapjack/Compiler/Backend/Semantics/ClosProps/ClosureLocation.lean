import Flapjack.Compiler.Backend.Semantics.ClosSem.Call

/-! Location restrictions for closure application. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- A partial or over-applied closure call has no direct location. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_none_loc"]
theorem destClosureNoneLoc (maxApp : Nat) (location : Option Nat) (function : Value)
    (values : List Value) (partialValue : Value) (body : ClosLang.Exp) (env rest : List Value) :
    (destClosure maxApp location function values = some (.partialApp partialValue) → location = none) ∧
    (destClosure maxApp location function values = some (.fullApp body env rest) ∧ rest ≠ [] →
      location = none) := by
  cases location with
  | none => simp
  | some address =>
    constructor
    · intro found
      cases function <;> simp only [destClosure] at found <;> try contradiction
      case closure loc supplied captured arity exp =>
        split at found <;> simp_all [checkLoc]
      case recclosure loc supplied captured fns index =>
        split at found <;> simp_all [checkLoc]
    · intro ⟨found, nonempty⟩
      cases function <;> simp only [destClosure] at found <;> try contradiction
      case closure loc supplied captured arity exp =>
        split at found <;> simp_all [checkLoc]
        have dropEmpty : values.reverse.drop values.length = [] := by simp
        rw [dropEmpty] at found
        simp_all
      case recclosure loc supplied captured fns index =>
        split at found <;> simp_all [checkLoc]
        have dropEmpty : values.reverse.drop values.length = [] := by simp
        rw [dropEmpty] at found
        simp_all

end Flapjack.Compiler.Backend.ClosProps
