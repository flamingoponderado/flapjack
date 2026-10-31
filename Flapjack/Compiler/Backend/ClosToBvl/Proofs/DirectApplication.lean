import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact

/-! Source-side call shapes used for known-location application simulation. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- A known-location application requires an exact arity and no previously
supplied arguments. This is Flapjack proof infrastructure for direct calls. -/
theorem checkLoc_direct (maxApp address : Nat) (location : Option Nat)
    (parameters arguments supplied : Nat)
    (valid : checkLoc maxApp (some address) location parameters arguments supplied = true) :
    parameters = arguments ∧ supplied = 0 ∧ location = some address := by
  simp only [checkLoc, decide_eq_true_eq] at valid
  exact ⟨valid.1, valid.2.1, valid.2.2.symm⟩

/-- A known-location application cannot produce a partial closure. -/
theorem destClosure_direct_not_partial (maxApp address : Nat) (function : Value)
    (args : List Value) (partialValue : Value) :
    destClosure maxApp (some address) function args ≠ some (.partialApp partialValue) := by
  intro result
  cases function <;> simp only [destClosure] at result <;> try contradiction
  case closure location supplied captured arity body =>
    split at result
    · rename_i valid
      have facts := checkLoc_direct maxApp address location arity args.length supplied.length (by
        simp only [Bool.and_eq_true] at valid
        exact valid.1)
      split at result
      · omega
      · simp at result
    · simp at result
  case recclosure location supplied captured functions index =>
    split at result
    · simp at result
    · rename_i arity body found
      split at result
      · rename_i valid
        have facts := checkLoc_direct maxApp address (location.map (fun loc => 2 * index + loc))
          arity args.length supplied.length (by
            simp only [Bool.and_eq_true] at valid
            exact valid.1)
        split at result
        · omega
        · simp at result
      · simp at result

/-- A known-location full application consumes the complete argument list. -/
theorem destClosure_direct_remaining_nil (maxApp address : Nat) (function : Value)
    (args env rest : List Value) (body : ClosLang.Exp)
    (result : destClosure maxApp (some address) function args = some (.fullApp body env rest)) :
    rest = [] := by
  cases function <;> simp only [destClosure] at result <;> try contradiction
  case closure location supplied captured arity expression =>
    split at result
    · rename_i valid
      have facts := checkLoc_direct maxApp address location arity args.length supplied.length (by
        simp only [Bool.and_eq_true] at valid
        exact valid.1)
      split at result
      · simp at result
      · simp only [Option.some.injEq, AppKind.fullApp.injEq] at result
        rcases result with ⟨_, _, rfl⟩
        have needed : arity - supplied.length = args.length := by omega
        simp [needed]
    · simp at result
  case recclosure location supplied captured functions index =>
    split at result
    · simp at result
    · rename_i arity expression found
      split at result
      · rename_i valid
        have facts := checkLoc_direct maxApp address (location.map (fun loc => 2 * index + loc))
          arity args.length supplied.length (by
            simp only [Bool.and_eq_true] at valid
            exact valid.1)
        split at result
        · simp at result
        · simp only [Option.some.injEq, AppKind.fullApp.injEq] at result
          rcases result with ⟨_, _, rfl⟩
          have needed : arity - supplied.length = args.length := by omega
          simp [needed]
      · simp at result


/-- Successful known-location ordinary closure calls supply all arguments
at once and enter the closure body with those arguments and its environment. -/
theorem destClosure_direct_closure (maxApp address : Nat) (location : Option Nat)
    (supplied captured args : List Value) (arity : Nat) (body : ClosLang.Exp) (application : AppKind)
    (result : destClosure maxApp (some address) (.closure location supplied captured arity body) args =
      some application) :
    location = some address ∧ supplied = [] ∧ arity = args.length ∧ args ≠ [] ∧
      application = .fullApp body (args ++ captured) [] := by
  simp only [destClosure] at result
  split at result
  · rename_i valid
    have facts := checkLoc_direct maxApp address location arity args.length supplied.length (by
      simp only [Bool.and_eq_true] at valid
      exact valid.1)
    have suppliedNil : supplied = [] := List.length_eq_zero_iff.mp facts.2.1
    have nonempty : args ≠ [] := by
      intro empty
      simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
      simp [suppliedNil, empty, facts.1] at valid
    subst supplied
    have arityEq := facts.1
    subst arity
    have take : args.reverse.take args.length = args.reverse := by simpa using (List.take_length (l := args.reverse))
    have drop : args.reverse.drop args.length = [] := by simp
    simp [take, drop] at result
    exact ⟨facts.2.2, rfl, rfl, nonempty, result.symm⟩
  · simp at result

/-- Successful known-location recursive closure calls select the indexed code
entry and pass the complete argument list and recursive environment. -/
theorem destClosure_direct_recclosure (maxApp address : Nat) (location : Option Nat)
    (supplied captured args : List Value) (functions : List (Nat × ClosLang.Exp)) (index : Nat)
    (application : AppKind)
    (result : destClosure maxApp (some address) (.recclosure location supplied captured functions index) args =
      some application) :
    ∃ arity body, functions[index]? = some (arity, body) ∧
      location.map (fun loc => 2 * index + loc) = some address ∧ supplied = [] ∧
      arity = args.length ∧ args ≠ [] ∧
      application = .fullApp body
        (args ++ (List.range functions.length).map (fun i => Value.recclosure location [] captured functions i) ++ captured) [] := by
  simp only [destClosure] at result
  split at result
  · simp at result
  · rename_i arity body found
    split at result
    · rename_i valid
      have facts := checkLoc_direct maxApp address (location.map (fun loc => 2 * index + loc))
        arity args.length supplied.length (by
          simp only [Bool.and_eq_true] at valid
          exact valid.1)
      have suppliedNil : supplied = [] := List.length_eq_zero_iff.mp facts.2.1
      have nonempty : args ≠ [] := by
        intro empty
        simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
        simp [suppliedNil, empty, facts.1] at valid
      subst supplied
      have arityEq := facts.1
      subst arity
      have take : args.reverse.take args.length = args.reverse := by simpa using (List.take_length (l := args.reverse))
      have drop : args.reverse.drop args.length = [] := by simp
      simp [take, drop] at result
      exact ⟨args.length, body, found, facts.2.2, rfl, rfl, nonempty, by simpa [List.append_assoc] using result.symm⟩
    · simp at result



/-- A saturated known-location call has no application continuation: after
its clock cost it is exactly the clock-clamped evaluation of the body. -/
theorem evaluateApp_direct_full {C F : Type} (address : Nat) (function : Value)
    (args env rest : List Value) (body : ClosLang.Exp) (state : State C F)
    (nonempty : args ≠ [])
    (found : destClosure state.maxApp (some address) function args = some (.fullApp body env rest)) :
    evaluateApp (some address) function args state =
      if state.clock < args.length then (.err (.abort .timeoutError), { state with clock := 0 })
      else fixClock (decClock args.length state) (evaluate [body] env (decClock args.length state)) := by
  have empty := destClosure_direct_remaining_nil state.maxApp address function args env rest body found
  subst rest
  cases args with
  | nil => contradiction
  | cons first tail =>
    rw [evaluateApp]
    rw [found]
    simp only [List.length_nil, Nat.sub_zero]
    split
    · rfl
    · cases run : fixClock (decClock (first :: tail).length state)
          (evaluate [body] env (decClock (first :: tail).length state)) with
      | mk result next =>
        cases result with
        | err error => rfl
        | val values =>
          cases values with
          | nil => rfl
          | cons value rest =>
            cases rest with
            | nil => simp [evaluateApp]
            | cons other remaining => rfl

end Flapjack.Compiler.Backend.ClosSem
