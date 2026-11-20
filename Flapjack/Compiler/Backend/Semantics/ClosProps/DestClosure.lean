module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Call
public import Flapjack.Compiler.Backend.Semantics.ClosProps.SimpleRelations
public import Flapjack.HolArb

@[expose] public section

/-! Shared unfolding of the recursive-closure clause of `destClosure` at a
known function entry. Flapjack proof infrastructure; no separately named HOL
declaration. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Unfold recursive-closure inspection at a known function entry. This helper
has no standalone HOL declaration. -/
theorem destClosure_rec_found (maxApp : Nat) (requested location : Option Nat)
    (supplied env args : List Value) (functions : List (Nat × ClosLang.Exp))
    (index arity : Nat) (body : ClosLang.Exp)
    (found : functions[index]? = some (arity, body)) :
    destClosure maxApp requested (.recclosure location supplied env functions index) args =
      if checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
          arity args.length supplied.length && supplied.length < arity then
        if args.length + supplied.length < arity then
          some (.partialApp (.recclosure location (args ++ supplied) env functions index))
        else
          some (.fullApp body
            ((args.reverse.take (arity - supplied.length)).reverse ++
              (supplied ++ ((List.range functions.length).map
                (fun i => Value.recclosure location [] env functions i) ++ env)))
            ((args.reverse.drop (arity - supplied.length)).reverse))
      else none := by
  simp only [destClosure, found]
  split
  · split <;> simp [List.append_assoc]
  · rfl

/-- The value carrier is inhabited, so HOL's unspecified clauses of a partial
function over values have a Lean instance to draw on. -/
local instance destClosureValueInhabited : Nonempty Value := ⟨Value.number 0⟩

/-- Prepend already-applied arguments to a partially applied closure. HOL
completes the missing constructors with `ARB`; here they share the opaque
`holArb` value at the closure carrier. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "clo_add_partial_args_def"]
noncomputable def cloAddPartialArgs (args : List Value) : Value → Value
  | .closure loc supplied env arity body => .closure loc (args ++ supplied) env arity body
  | .recclosure loc supplied env functions index =>
      .recclosure loc (args ++ supplied) env functions index
  | _ => holArb Value

/-- Adding no arguments leaves a closure unchanged. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "is_closure_add_partial_args_nil"]
theorem isClosureValue_cloAddPartialArgs_nil (v : Value) (closed : isClosureValue v) :
    cloAddPartialArgs [] v = v := by
  cases v <;> simp_all [cloAddPartialArgs, isClosureValue]

/-- A successful partial application returns a closure value. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_partial_is_closure"]
theorem destClosure_partial_isClosure (maxApp : Nat) (l : Option Nat) (v : Value)
    (vs : List Value) (v' : Value)
    (run : destClosure maxApp l v vs = some (.partialApp v')) : isClosureValue v' := by
  cases v <;> simp only [destClosure] at run <;> try contradiction
  case closure location supplied env arity body =>
    split at run
    · split at run
      · simp only [Option.some.injEq, AppKind.partialApp.injEq] at run
        subst run
        exact trivial
      · simp at run
    · simp at run
  case recclosure location supplied env functions index =>
    split at run
    · simp at run
    · split at run
      · split at run
        · simp only [Option.some.injEq, AppKind.partialApp.injEq] at run
          subst run
          exact trivial
        · simp at run
      · simp at run

/-- A successful split of an application starts from a closure value. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_is_closure"]
theorem destClosure_isClosure (maxApp : Nat) (lopt : Option Nat) (f : Value)
    (vs : List Value) (r : AppKind)
    (run : destClosure maxApp lopt f vs = some r) : isClosureValue f := by
  cases f <;> simp_all [destClosure, isClosureValue]

/-- A full application consumes arguments, so its remainder is shorter. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_rest_length"]
theorem destClosure_rest_length (maxApp : Nat) (f : Value) (args : List Value)
    (e : ClosLang.Exp) (l rest : List Value)
    (run : destClosure maxApp none f args = some (.fullApp e l rest)) :
    rest.length < args.length :=
  destClosure_full_remaining_lt maxApp none f args l rest e run

/-- A full application with a nonempty remainder fits the maximum arity. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_full_maxapp"]
theorem destClosure_full_maxapp (maxApp : Nat) (c : Value) (vs : List Value)
    (b : ClosLang.Exp) (env r : List Value)
    (h : destClosure maxApp none c vs = some (.fullApp b env r) ∧ r ≠ []) :
    vs.length ≤ maxApp := by
  obtain ⟨run, _⟩ := h
  cases c <;> simp only [destClosure] at run <;> try contradiction
  case closure location supplied env0 arity body =>
    split at run
    · rename_i valid
      split at run
      · simp at run
      · simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
        simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
        simpa [checkLoc] using valid.1
    · simp at run
  case recclosure location supplied env0 functions index =>
    split at run
    · simp at run
    · split at run
      · rename_i valid
        split at run
        · simp at run
        · simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          simpa [checkLoc] using valid.1
      · simp at run

/-- Appending arguments cannot turn a failed split into a successful one. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_none_append"]
theorem destClosure_none_append {α : Type} (maxApp : Nat) (_l : α) (f : Value)
    (args1 args2 : List Value)
    (run : destClosure maxApp none f args2 = none) :
    destClosure maxApp none f (args1 ++ args2) = none := by
  cases f <;> simp only [destClosure] at run ⊢
  case closure location supplied env arity body =>
    have hfalse : (checkLoc maxApp none location arity args2.length supplied.length &&
        decide (supplied.length < arity)) = false := by
      by_contra hne
      rw [Bool.not_eq_false] at hne
      rw [hne] at run
      by_cases h2 : args2.length + supplied.length < arity
      · rw [if_pos h2] at run
        exact absurd run (by simp)
      · rw [if_neg h2] at run
        exact absurd run (by simp)
    have hfalse' : (checkLoc maxApp none location arity (args1 ++ args2).length
        supplied.length && decide (supplied.length < arity)) = false := by
      rw [Bool.and_eq_false_iff] at hfalse ⊢
      rcases hfalse with h | h
      · left
        simp only [checkLoc, decide_eq_false_iff_not, List.length_append] at h ⊢
        omega
      · right
        exact h
    rw [hfalse']
    rfl
  case recclosure location supplied env functions index =>
    cases hfound : functions[index]? with
    | none => rfl
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      rw [hfound] at run
      simp only [] at run ⊢
      have hfalse : (checkLoc maxApp none (location.map (fun loc => 2 * index + loc)) arity
          args2.length supplied.length && decide (supplied.length < arity)) = false := by
        by_contra hne
        rw [Bool.not_eq_false] at hne
        rw [hne] at run
        by_cases h2 : args2.length + supplied.length < arity
        · rw [if_pos h2] at run
          exact absurd run (by simp)
        · rw [if_neg h2] at run
          exact absurd run (by simp)
      have hfalse' : (checkLoc maxApp none (location.map (fun loc => 2 * index + loc)) arity
          (args1 ++ args2).length supplied.length && decide (supplied.length < arity)) = false := by
        rw [Bool.and_eq_false_iff] at hfalse ⊢
        rcases hfalse with h | h
        · left
          simp only [checkLoc, decide_eq_false_iff_not, List.length_append] at h ⊢
          omega
        · right
          exact h
      rw [hfalse']
      rfl

/-- Within the maximum arity, a failed split of a longer list implies a failed
split of the shorter tail. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_none_append2"]
theorem destClosure_none_append2 {α : Type} (maxApp : Nat) (_l : α) (f : Value)
    (args1 args2 : List Value)
    (h : args1.length + args2.length ≤ maxApp ∧
      destClosure maxApp none f (args1 ++ args2) = none) :
    destClosure maxApp none f args2 = none := by
  obtain ⟨bound, run⟩ := h
  cases f <;> simp only [destClosure] at run ⊢
  case closure location supplied env arity body =>
    have hfalse : (checkLoc maxApp none location arity (args1 ++ args2).length
        supplied.length && decide (supplied.length < arity)) = false := by
      by_contra hne
      rw [Bool.not_eq_false] at hne
      rw [hne] at run
      by_cases h2 : (args1 ++ args2).length + supplied.length < arity
      · rw [if_pos h2] at run
        exact absurd run (by simp)
      · rw [if_neg h2] at run
        exact absurd run (by simp)
    have hcheck : checkLoc maxApp none location arity (args1 ++ args2).length
        supplied.length = true := by
      simp only [checkLoc, decide_eq_true_eq, List.length_append]
      omega
    have hsmall : decide (supplied.length < arity) = false := by
      rw [Bool.and_eq_false_iff] at hfalse
      rcases hfalse with h | h
      · rw [h] at hcheck
        exact absurd hcheck (by simp)
      · exact h
    have hgoal : (checkLoc maxApp none location arity args2.length supplied.length &&
        decide (supplied.length < arity)) = false := by
      rw [hsmall]
      simp
    rw [hgoal]
    rfl
  case recclosure location supplied env functions index =>
    cases hfound : functions[index]? with
    | none => rfl
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      rw [hfound] at run
      simp only [] at run ⊢
      have hfalse : (checkLoc maxApp none (location.map (fun loc => 2 * index + loc)) arity
          (args1 ++ args2).length supplied.length && decide (supplied.length < arity)) = false := by
        by_contra hne
        rw [Bool.not_eq_false] at hne
        rw [hne] at run
        by_cases h2 : (args1 ++ args2).length + supplied.length < arity
        · rw [if_pos h2] at run
          exact absurd run (by simp)
        · rw [if_neg h2] at run
          exact absurd run (by simp)
      have hcheck : checkLoc maxApp none (location.map (fun loc => 2 * index + loc)) arity
          (args1 ++ args2).length supplied.length = true := by
        simp only [checkLoc, decide_eq_true_eq, List.length_append]
        omega
      have hsmall : decide (supplied.length < arity) = false := by
        rw [Bool.and_eq_false_iff] at hfalse
        rcases hfalse with h | h
        · rw [h] at hcheck
          exact absurd hcheck (by simp)
        · exact h
      have hgoal : (checkLoc maxApp none (location.map (fun loc => 2 * index + loc)) arity
          args2.length supplied.length && decide (supplied.length < arity)) = false := by
        rw [hsmall]
        simp
      rw [hgoal]
      rfl

/-- Flapjack helper for `stage_partial_app`: a successful partial split returns
exactly the argument-prefixed closure. There is no separate HOL declaration for
this shape; it is derived here so the source's staging lemma can be proved from
the list equation alone. -/
theorem destClosure_partial_eq (maxApp : Nat) (requested : Option Nat) (v : Value)
    (args : List Value) (c' : Value)
    (run : destClosure maxApp requested v args = some (.partialApp c')) :
    c' = cloAddPartialArgs args v := by
  cases v <;> simp only [destClosure] at run <;> try contradiction
  case closure loc supplied env arity body =>
    split at run
    · split at run
      · simp only [Option.some.injEq, AppKind.partialApp.injEq] at run
        simp only [cloAddPartialArgs]
        exact run.symm
      · exact absurd run (by simp)
    · exact absurd run (by simp)
  case recclosure loc supplied env functions index =>
    split at run
    · contradiction
    · split at run
      · split at run
        · simp only [Option.some.injEq, AppKind.partialApp.injEq] at run
          simp only [cloAddPartialArgs]
          exact run.symm
        · exact absurd run (by simp)
      · exact absurd run (by simp)

end Flapjack.Compiler.Backend.ClosProps
