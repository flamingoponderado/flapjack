import Flapjack.Compiler.Backend.Semantics.ClosSem.State

/-! Closure application and code lookup for the closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosSem

/-- A direct call accepts a code entry only at its declared arity. The
finite-map representation still requires cross-language review. -/
def findCode {α : Type} (location : Nat) (args : List α)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : Option (List α × ClosLang.Exp) := do
  let (arity, body) ← code.lookup location
  if args.length = arity then some (args, body) else none

/-- Check the optional direct-call location and application arity. This
proof-side definition remains untagged pending source correspondence review. -/
def checkLoc (maxApp : Nat) (requested location : Option Nat)
    (parameters arguments supplied : Nat) : Bool :=
  match requested with
  | none => decide (arguments ≤ maxApp)
  | some address => decide (parameters = arguments ∧ supplied = 0 ∧ some address = location)

/-- Result of examining a closure application. -/
inductive AppKind where
  | partialApp : Value → AppKind
  | fullApp : ClosLang.Exp → List Value → List Value → AppKind

/-- Split argument lists exactly as the closure evaluator does, allowing
partial and over-application and constructing all recursive closures. -/
def destClosure (maxApp : Nat) (requested : Option Nat) (function : Value)
    (args : List Value) : Option AppKind :=
  match function with
  | .closure location supplied env arity body =>
    if checkLoc maxApp requested location arity args.length supplied.length && supplied.length < arity then
      if args.length + supplied.length < arity then
        some (.partialApp (.closure location (args ++ supplied) env arity body))
      else
        let needed := arity - supplied.length
        some (.fullApp body (args.reverse.take needed |>.reverse |>.append (supplied ++ env))
          (args.reverse.drop needed |>.reverse))
    else none
  | .recclosure location supplied env functions index =>
    match functions[index]? with
    | none => none
    | some (arity, body) =>
      let codeLocation := location.map (fun loc => 2 * index + loc)
      if checkLoc maxApp requested codeLocation arity args.length supplied.length && supplied.length < arity then
        if args.length + supplied.length < arity then
          some (.partialApp (.recclosure location (args ++ supplied) env functions index))
        else
          let needed := arity - supplied.length
          let recursive := (List.range functions.length).map (fun i => Value.recclosure location [] env functions i)
          some (.fullApp body (args.reverse.take needed |>.reverse |>.append (supplied ++ recursive ++ env))
            (args.reverse.drop needed |>.reverse))
      else none
  | _ => none

/-- A full application consumes at least one argument. This ensures that
repeated application of an over-applied result can be well founded. -/
theorem destClosure_full_remaining_lt (maxApp : Nat) (requested : Option Nat)
    (function : Value) (args env rest : List Value) (body : ClosLang.Exp)
    (result : destClosure maxApp requested function args = some (.fullApp body env rest)) :
    rest.length < args.length := by
  cases function <;> simp only [destClosure] at result <;> try contradiction
  case closure location supplied captured arity expression =>
    split at result
    · rename_i valid
      split at result
      · simp at result
      · simp only [Option.some.injEq, AppKind.fullApp.injEq] at result
        rcases result with ⟨_, _, rfl⟩
        simp only [List.length_reverse, List.length_drop]
        have suppliedBound : supplied.length < arity := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          exact valid.2
        omega
    · simp at result
  case recclosure location supplied captured functions index =>
    split at result
    · simp at result
    · rename_i arity expression found
      split at result
      · rename_i valid
        split at result
        · simp at result
        · simp only [Option.some.injEq, AppKind.fullApp.injEq] at result
          rcases result with ⟨_, _, rfl⟩
          simp only [List.length_reverse, List.length_drop]
          have suppliedBound : supplied.length < arity := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            exact valid.2
          omega
      · simp at result

/-- Gather selected environment values in order, rejecting an invalid index.
This helper is proof-side infrastructure for closure environment restriction. -/
def lookupVars {α : Type} : List Nat → List α → Option (List α)
  | [], _ => some []
  | index :: indices, env => do
    let value ← env[index]?
    let values ← lookupVars indices env
    some (value :: values)

/-- Restrict an environment when requested by the closure optimizer. -/
def closEnv (restrict : Bool) (names : List Nat) (env : List Value) : Option (List Value) :=
  if restrict then lookupVars names env else some env

/-- Construct the recursive closure bundle over the selected environment. -/
def buildRecc (restrict : Bool) (location : Option Nat) (env : List Value)
    (names : List Nat) (functions : List (Nat × ClosLang.Exp)) : Option (List Value) := do
  let captured ← closEnv restrict names env
  pure ((List.range functions.length).map (fun i => .recclosure location [] captured functions i))

end Flapjack.Compiler.Backend.ClosSem
