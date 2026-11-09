module

public import Flapjack.Compiler.Backend.ClosNumber
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

@[expose] public section

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

/-- Numbering preserves the length of an expression list. -/
theorem renumberList_length (expressions : List Exp) (start : Nat) :
    (renumberList start expressions).2.length = expressions.length := by
  cases expressions with
  | nil => simp [renumberList]
  | cons first rest => simp [renumberList, renumberList_length rest]
termination_by sizeOf expressions

mutual

/-- Numbering never moves the next available location backwards. -/
theorem renumber_start_le (expression : Exp) (start : Nat) :
    start ≤ (renumber start expression).1 := by
  cases expression with
  | var trace n => simp [renumber]
  | ifThenElse trace condition yes no =>
    simp only [renumber]
    have a := renumber_start_le condition start
    have b := renumber_start_le yes (renumber start condition).1
    have c := renumber_start_le no (renumber (renumber start condition).1 yes).1
    omega
  | «let» trace bindings body =>
    simp only [renumber]
    have a := renumberList_start_le bindings start
    have b := renumber_start_le body (renumberList start bindings).1
    omega
  | raise trace body => simpa [renumber] using renumber_start_le body start
  | handle trace body handler =>
    simp only [renumber]
    have a := renumber_start_le body start
    have b := renumber_start_le handler (renumber start body).1
    omega
  | tick trace body => simpa [renumber] using renumber_start_le body start
  | call trace ticks location args => simpa [renumber] using renumberList_start_le args start
  | app trace location function args =>
    simp only [renumber]
    have a := renumber_start_le function start
    have b := renumberList_start_le args (renumber start function).1
    omega
  | fn name location vars arity body =>
    simp only [renumber]
    have a := renumber_start_le body start
    omega
  | letrec names location vars functions body =>
    simp only [renumber]
    have a := renumberFuns_start_le functions start
    have b := renumber_start_le body ((renumberFuns start functions).1 +
      2 * (renumberFuns start functions).2.length)
    omega
  | op trace op args => simpa [renumber] using renumberList_start_le args start
termination_by sizeOf expression

theorem renumberList_start_le (expressions : List Exp) (start : Nat) :
    start ≤ (renumberList start expressions).1 := by
  cases expressions with
  | nil => simp [renumberList]
  | cons first rest =>
    simp only [renumberList]
    have a := renumber_start_le first start
    have b := renumberList_start_le rest (renumber start first).1
    omega
termination_by sizeOf expressions

theorem renumberFuns_start_le (functions : List (Nat × Exp)) (start : Nat) :
    start ≤ (renumberFuns start functions).1 := by
  cases functions with
  | nil => simp [renumberFuns]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [renumberFuns]
      have a := renumber_start_le body start
      have b := renumberFuns_start_le rest (renumber start body).1
      omega
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

/-- Numbering never decreases the next location, for both source traversals. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_inc"]
theorem renumberCodeLocs_inc :
    (∀ n es, n ≤ (renumberList n es).1) ∧
    (∀ n e, n ≤ (renumber n e).1) :=
  ⟨fun n es => renumberList_start_le es n, fun n e => renumber_start_le e n⟩

/-- The same lower bound expressed for explicitly returned state pairs. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_imp_inc"]
theorem renumberCodeLocs_imp_inc (n : Nat) (es : List Exp) (m : Nat) (vs : List Exp)
    (e : Exp) (z : Nat) (v : Exp) :
    (renumberList n es = (m, vs) → n ≤ m) ∧
    (renumber n e = (z, v) → n ≤ z) := by
  constructor
  · intro h
    simpa [h] using renumberCodeLocs_inc.1 n es
  · intro h
    simpa [h] using renumberCodeLocs_inc.2 n e

/-- Closure numbering fills every function-code location, both for expression
lists and for individual expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_every_Fn_SOME"]
theorem renumberCodeLocs_everyFnSome :
    (∀ start expressions, everyFnLocationSome (renumberList start expressions).2) ∧
    (∀ start expression, everyFnLocationSome [(renumber start expression).2]) := by
  constructor
  · intro start expressions
    exact renumberList_locations expressions start
  · intro start expression
    simpa [everyFnLocationSome] using renumber_locations expression start

end Flapjack.Compiler.Backend.ClosNumber
