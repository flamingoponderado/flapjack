import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic

/-! Preservation of absent capture annotations by closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

mutual

/-- Numbering changes code locations but does not add capture annotations. -/
theorem renumber_varsNone (expression : Exp) (start : Nat) :
    fnVarsNoneExp (renumber start expression).2 ↔ fnVarsNoneExp expression := by
  cases expression with
  | var trace n => simp [renumber, fnVarsNoneExp]
  | ifThenElse trace condition yes no =>
    simp [renumber, fnVarsNoneExp, renumber_varsNone condition, renumber_varsNone yes, renumber_varsNone no]
  | «let» trace bindings body =>
    simp [renumber, fnVarsNoneExp, renumberList_varsNone bindings, renumber_varsNone body]
  | raise trace body => simp [renumber, fnVarsNoneExp, renumber_varsNone body]
  | handle trace body handler =>
    simp [renumber, fnVarsNoneExp, renumber_varsNone body, renumber_varsNone handler]
  | tick trace body => simp [renumber, fnVarsNoneExp, renumber_varsNone body]
  | call trace ticks location args => simp [renumber, fnVarsNoneExp, renumberList_varsNone args]
  | app trace location function args =>
    simp [renumber, fnVarsNoneExp, renumber_varsNone function, renumberList_varsNone args]
  | fn name location vars arity body => simp [renumber, fnVarsNoneExp, renumber_varsNone body]
  | letrec names location vars functions body =>
    simp [renumber, fnVarsNoneExp, renumberFuns_varsNone functions, renumber_varsNone body]
  | op trace op args => simp [renumber, fnVarsNoneExp, renumberList_varsNone args]
termination_by sizeOf expression

/-- The same invariant for lists of expressions. -/
theorem renumberList_varsNone (expressions : List Exp) (start : Nat) :
    everyFnVarsNone (renumberList start expressions).2 ↔ everyFnVarsNone expressions := by
  cases expressions with
  | nil => simp [renumberList, everyFnVarsNone]
  | cons first rest =>
    simp [renumberList, everyFnVarsNone, renumber_varsNone first, renumberList_varsNone rest]
termination_by sizeOf expressions

/-- The same invariant for recursive function bundles. -/
theorem renumberFuns_varsNone (functions : List (Nat × Exp)) (start : Nat) :
    fnVarsNoneFuns (renumberFuns start functions).2 ↔ fnVarsNoneFuns functions := by
  cases functions with
  | nil => simp [renumberFuns, fnVarsNoneFuns]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp [renumberFuns, fnVarsNoneFuns, renumber_varsNone body, renumberFuns_varsNone rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

/-- Incremental numbering's name marker also leaves captures absent. -/
theorem compileInc_varsNone (start : Nat) (expressions : List Exp) :
    everyFnVarsNone (compileInc start expressions).2 ↔ everyFnVarsNone expressions := by
  simp [compileInc, everyFnVarsNone, fnVarsNoneExp, renumberList_varsNone]

end Flapjack.Compiler.Backend.ClosNumber
