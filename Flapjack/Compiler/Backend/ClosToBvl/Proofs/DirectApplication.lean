module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact

@[expose] public section

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



/-- A successful known-location selection is also the generic selection when
the closure's arity satisfies the generic maximum-application bound. -/
theorem destClosure_direct_generic (maxApp address : Nat) (function : Value)
    (args : List Value) (application : AppKind) (bound : args.length ≤ maxApp)
    (found : destClosure maxApp (some address) function args = some application) :
    destClosure maxApp none function args = some application := by
  cases function <;> simp only [destClosure] at found <;> try contradiction
  case closure location supplied captured arity body =>
    have shape := destClosure_direct_closure maxApp address location supplied captured args arity body application (by
      simpa only [destClosure] using found)
    obtain ⟨rfl, rfl, arityEq, nonempty, rfl⟩ := shape
    have positive : 0 < args.length := List.length_pos_iff.mpr nonempty
    have take : args.reverse.take args.length = args.reverse := by simpa using (List.take_length (l := args.reverse))
    simp [destClosure, checkLoc, bound, arityEq, positive, take]
  case recclosure location supplied captured functions index =>
    have shape := destClosure_direct_recclosure maxApp address location supplied captured args functions index application (by
      simpa only [destClosure] using found)
    obtain ⟨arity, body, selected, locationEq, rfl, arityEq, nonempty, rfl⟩ := shape
    have positive : 0 < args.length := List.length_pos_iff.mpr nonempty
    have take : args.reverse.take args.length = args.reverse := by simpa using (List.take_length (l := args.reverse))
    rw [arityEq] at selected
    simp [destClosure, selected, checkLoc, bound, positive, take, List.append_assoc]

/-- Given a successful direct selection, generic and known-location source
application have identical execution, including timeout and clock clamping. -/
theorem evaluateApp_direct_eq_generic {C F : Type} (address : Nat) (function : Value)
    (args : List Value) (state : State C F) (application : AppKind)
    (bound : args.length ≤ state.maxApp)
    (found : destClosure state.maxApp (some address) function args = some application) :
    evaluateApp (some address) function args state = evaluateApp none function args state := by
  have generic := destClosure_direct_generic state.maxApp address function args application bound found
  cases application with
  | partialApp partialValue => exact False.elim (destClosure_direct_not_partial _ _ _ _ _ found)
  | fullApp body env rest =>
    have empty := destClosure_direct_remaining_nil state.maxApp address function args env rest body found
    subst rest
    have nonempty : args ≠ [] := by
      have h := destClosure_full_remaining_lt state.maxApp (some address) function args env [] body found
      intro empty
      simp [empty] at h
    cases args with
    | nil => contradiction
    | cons first tail =>
      conv_lhs => rw [evaluateApp, found]
      conv_rhs => rw [evaluateApp, generic]
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
