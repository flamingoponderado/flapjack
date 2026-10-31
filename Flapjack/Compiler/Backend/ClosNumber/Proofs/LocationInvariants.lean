import Flapjack.Compiler.Backend.ClosNumber
import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations

/-! Function-location invariants of closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

mutual

/-- Flapjack helper: numbering an expression assigns every function and
recursive group a code location. -/
theorem renumber_locations (expression : Exp) (start : Nat) :
    fnLocationSomeExp (renumber start expression).2 := by
  cases expression with
  | var trace n => simp [renumber, fnLocationSomeExp]
  | ifThenElse trace condition yes no =>
    simp [renumber, fnLocationSomeExp, renumber_locations condition, renumber_locations yes, renumber_locations no]
  | «let» trace bindings body =>
    simp [renumber, fnLocationSomeExp, renumberList_locations bindings, renumber_locations body]
  | raise trace body => simp [renumber, fnLocationSomeExp, renumber_locations body]
  | handle trace body handler =>
    simp [renumber, fnLocationSomeExp, renumber_locations body, renumber_locations handler]
  | tick trace body => simp [renumber, fnLocationSomeExp, renumber_locations body]
  | call trace ticks location args => simp [renumber, fnLocationSomeExp, renumberList_locations args]
  | app trace location function args =>
    simp [renumber, fnLocationSomeExp, renumber_locations function, renumberList_locations args]
  | fn name location vars arity body => simp [renumber, fnLocationSomeExp, renumber_locations body]
  | letrec names location vars functions body =>
    simp [renumber, fnLocationSomeExp, renumberFuns_locations functions, renumber_locations body]
  | op trace op args => simp [renumber, fnLocationSomeExp, renumberList_locations args]
termination_by sizeOf expression

/-- Flapjack helper for the list traversal of closure numbering. -/
theorem renumberList_locations (expressions : List Exp) (start : Nat) :
    everyFnLocationSome (renumberList start expressions).2 := by
  cases expressions with
  | nil => simp [renumberList, everyFnLocationSome]
  | cons first rest =>
    simp [renumberList, everyFnLocationSome, renumber_locations first, renumberList_locations rest]
termination_by sizeOf expressions

/-- Flapjack helper for closure numbering inside recursive groups. -/
theorem renumberFuns_locations (functions : List (Nat × Exp)) (start : Nat) :
    fnLocationSomeFuns (renumberFuns start functions).2 := by
  cases functions with
  | nil => simp [renumberFuns, fnLocationSomeFuns]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp [renumberFuns, fnLocationSomeFuns, renumber_locations body, renumberFuns_locations rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

/-- Closure numbering fills every function-code location, both for expression
lists and for individual expressions. This source-shaped statement is untagged
pending typed HOL and numbering-carrier review. -/
theorem renumberCodeLocs_everyFnSome :
    (∀ start expressions, everyFnLocationSome (renumberList start expressions).2) ∧
    (∀ start expression, everyFnLocationSome [(renumber start expression).2]) := by
  constructor
  · intro start expressions
    exact renumberList_locations expressions start
  · intro start expression
    simpa [everyFnLocationSome] using renumber_locations expression start

/-- The incremental numbering wrapper also assigns every function location;
its leading name marker contains no closures. -/
theorem compileInc_locations (start : Nat) (expressions : List Exp) :
    everyFnLocationSome (compileInc start expressions).2 := by
  have locations := renumberList_locations expressions
    (let next := start + max expressions.length 1; if next % 2 = 0 then next else next + 1)
  simpa [compileInc, everyFnLocationSome, fnLocationSomeExp] using locations

/-- Every member of a location-annotated list is location-annotated. -/
theorem locations_member (expressions : List Exp) (expression : Exp)
    (locations : everyFnLocationSome expressions) (member : expression ∈ expressions) :
    everyFnLocationSome [expression] := by
  induction expressions with
  | nil => simp at member
  | cons first rest ih =>
    simp only [everyFnLocationSome] at locations
    simp only [List.mem_cons] at member
    cases member with
    | inl equal => subst expression; simpa [everyFnLocationSome] using locations.1
    | inr tail => exact ih locations.2 tail

end Flapjack.Compiler.Backend.ClosNumber
