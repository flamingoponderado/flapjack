import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMti
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
import Mathlib.Tactic

/-! Relationships between the pre-MTI and closure syntax predicates. -/
namespace Flapjack.Compiler.Backend.ClosProps

/-- Flapjack helper: pre-MTI expressions have no function-variable annotations
and no known-location or over-arity applications when the maximum is positive. -/
theorem noMti_syntactic (maxApp : Nat) (positive : 0 < maxApp) (e : ClosLang.Exp) :
    noMti e → fnVarsNoneExp e ∧ ¬ containsAppSomeExp maxApp e := by
  induction e using noMti.induct
      (motive2 := fun fs => noMtiFuns fs → fnVarsNoneFuns fs ∧ ¬ containsAppSomeFuns maxApp fs)
      (motive3 := fun es => noMtiList es → everyFnVarsNone es ∧ ¬ containsAppSome maxApp es)
  all_goals simp_all [noMti, noMtiList, noMtiFuns, fnVarsNoneExp, everyFnVarsNone,
    fnVarsNoneFuns, containsAppSomeExp, containsAppSome, containsAppSomeFuns]
  case case8 => omega
  case case11 t op args ih =>
    cases op <;> try simp_all [containsAppSomeExp]
    case thunkOp thunk =>
      cases thunk <;> simp_all [containsAppSomeExp]
      omega

/-- Flapjack helper lifting the syntax implications over an expression list. -/
theorem noMtiList_syntactic (maxApp : Nat) (positive : 0 < maxApp) (es : List ClosLang.Exp)
    (safe : ∀ e ∈ es, noMti e) : everyFnVarsNone es ∧ ¬ containsAppSome maxApp es := by
  induction es with
  | nil => simp [everyFnVarsNone, containsAppSome]
  | cons e es ih =>
    have head := noMti_syntactic maxApp positive e (safe e (by simp))
    have tail := ih (by intro x hx; exact safe x (by simp [hx]))
    simp [everyFnVarsNone, containsAppSome, head.1, head.2, tail.1, tail.2]

end Flapjack.Compiler.Backend.ClosProps
