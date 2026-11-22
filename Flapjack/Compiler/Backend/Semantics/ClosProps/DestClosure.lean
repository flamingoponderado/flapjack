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
  cases v
  all_goals simp_all [cloAddPartialArgs, isClosureValue]

/-- A successful partial application returns a closure value. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_partial_is_closure"]
theorem destClosure_partial_isClosure (maxApp : Nat) (l : Option Nat) (v : Value)
    (vs : List Value) (v' : Value)
    (run : destClosure maxApp l v vs = some (.partialApp v')) : isClosureValue v' := by
  cases v
  all_goals simp only [destClosure] at run
  all_goals try contradiction
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
  cases f
  all_goals simp_all [destClosure, isClosureValue]

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
  cases c
  all_goals simp only [destClosure] at run
  all_goals try contradiction
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
  cases f
  all_goals simp only [destClosure] at run ⊢
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
  cases f with
  | closure location supplied env arity body =>
    have hcheck : checkLoc maxApp none location arity (args1 ++ args2).length
        supplied.length = true := by
      simp only [checkLoc, decide_eq_true_eq, List.length_append]
      omega
    have hsmall : decide (supplied.length < arity) = false := by
      by_cases hs : supplied.length < arity
      · simp [destClosure, hs] at run
        split at run
        · simp_all
        · simp_all
      · simp [hs]
    simp [destClosure, hsmall]
  | recclosure location supplied env functions index =>
    cases hfound : functions[index]? with
    | none =>
      simp only [destClosure, hfound]
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      have hcheck : checkLoc maxApp none (location.map (fun loc => 2 * index + loc)) arity
          (args1 ++ args2).length supplied.length = true := by
        simp only [checkLoc, decide_eq_true_eq, List.length_append]
        omega
      have hsmall : decide (supplied.length < arity) = false := by
        by_cases hs : supplied.length < arity
        · simp [destClosure, hfound, hs] at run
          split at run
          · simp_all
          · simp_all
        · simp [hs]
      simp [destClosure, hfound, hsmall]
  | _ =>
    simp only [destClosure] at run ⊢

/-- Flapjack helper for `stage_partial_app`: a successful partial split returns
exactly the argument-prefixed closure. There is no separate HOL declaration for
this shape; it is derived here so the source's staging lemma can be proved from
the list equation alone. -/
theorem destClosure_partial_eq (maxApp : Nat) (requested : Option Nat) (v : Value)
    (args : List Value) (c' : Value)
    (run : destClosure maxApp requested v args = some (.partialApp c')) :
    c' = cloAddPartialArgs args v := by
  cases v
  all_goals simp only [destClosure] at run
  all_goals try contradiction
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

/-- Staging a partial application: if applying `rest ++ used` to `v` already
produces `c` with `rest` prepended, then applying `rest` to `c` alone produces
the same partial closure. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "stage_partial_app"]
theorem stagePartialApp (c : Value) (maxApp : Nat) (v : Value) (rest used : List Value)
    (h : isClosureValue c ∧
      destClosure maxApp none v (rest ++ used) = some (.partialApp (cloAddPartialArgs rest c))) :
    destClosure maxApp none c rest = some (.partialApp (cloAddPartialArgs rest c)) := by
  obtain ⟨hc, run⟩ := h
  cases v
  all_goals simp only [destClosure] at run
  all_goals try contradiction
  case closure loc supplied env arity body =>
    split at run
    · rename_i valid
      split at run
      · rename_i hpartial
        simp only [Option.some.injEq, AppKind.partialApp.injEq] at run
        cases c with
        | closure cloc csupplied cenv carity cbody =>
          simp only [cloAddPartialArgs] at run
          simp only [Value.closure.injEq] at run
          obtain ⟨rfl, hsupplied, rfl, rfl, rfl⟩ := run
          have hlen : rest.length + csupplied.length =
              (rest ++ used).length + supplied.length := by
            have := congrArg List.length hsupplied
            simp only [List.length_append] at this ⊢
            omega
          have hsmall : csupplied.length < arity := by omega
          have hcheck : checkLoc maxApp none loc arity rest.length csupplied.length = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc, List.length_append] at valid ⊢
            omega
          have hpartial2 : rest.length + csupplied.length < arity := by omega
          simp only [destClosure, cloAddPartialArgs]
          rw [if_pos (by simp [hcheck, hsmall]), if_pos hpartial2]
        | recclosure cloc csupplied cenv cfunctions cindex =>
          simp only [cloAddPartialArgs] at run
          simp at run
        | number n => simp [isClosureValue] at hc
        | word64 w => simp [isClosureValue] at hc
        | block t l => simp [isClosureValue] at hc
        | byteVector b => simp [isClosureValue] at hc
        | refPtr b n => simp [isClosureValue] at hc
      · simp at run
    · simp at run
  case recclosure loc supplied env functions index =>
    cases hfound : functions[index]? with
    | none =>
      simp only [hfound] at run
      simp at run
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      simp only [hfound] at run ⊢
      split at run
      · rename_i valid
        split at run
        · rename_i hpartial
          simp only [Option.some.injEq, AppKind.partialApp.injEq] at run
          cases c with
          | recclosure cloc csupplied cenv cfunctions cindex =>
            simp only [cloAddPartialArgs] at run
            simp only [Value.recclosure.injEq] at run
            obtain ⟨rfl, hsupplied, rfl, rfl, rfl⟩ := run
            have hlen : rest.length + csupplied.length =
                (rest ++ used).length + supplied.length := by
              have := congrArg List.length hsupplied
              simp only [List.length_append] at this ⊢
              omega
            have hsmall : csupplied.length < arity := by omega
            have hcheck : checkLoc maxApp none (loc.map (fun loc => 2 * index + loc)) arity
                rest.length csupplied.length = true := by
              simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc,
                List.length_append] at valid ⊢
              omega
            have hpartial2 : rest.length + csupplied.length < arity := by omega
            simp only [destClosure, cloAddPartialArgs, hfound]
            rw [if_pos (by simp [hcheck, hsmall]), if_pos hpartial2]
          | closure cloc csupplied cenv carity cbody =>
            simp only [cloAddPartialArgs] at run
            simp at run
          | number n => simp [isClosureValue] at hc
          | word64 w => simp [isClosureValue] at hc
          | block t l => simp [isClosureValue] at hc
          | byteVector b => simp [isClosureValue] at hc
          | refPtr b n => simp [isClosureValue] at hc
        · simp at run
      · simp at run

/-- Appending arguments within the maximum arity keeps a full application full
and only extends its remainder. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_full_addargs"]
theorem destClosure_full_addargs (maxApp : Nat) (c : Value) (vs : List Value)
    (b : ClosLang.Exp) (env r more : List Value)
    (h : destClosure maxApp none c vs = some (.fullApp b env r) ∧
      more.length + vs.length ≤ maxApp) :
    destClosure maxApp none c (more ++ vs) = some (.fullApp b env (more ++ r)) := by
  obtain ⟨run, bound⟩ := h
  cases c
  all_goals simp only [destClosure] at run
  all_goals try contradiction
  case closure loc supplied cenv arity body =>
    split at run
    · rename_i valid
      split at run
      · simp at run
      · rename_i hfull
        simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
        obtain ⟨rfl, henv, hrest⟩ := run
        simp_all [destClosure, checkLoc, Bool.and_eq_true, decide_eq_true_eq,
          List.take_append_of_le_length, List.drop_append_of_le_length,
          List.reverse_append, List.reverse_reverse]
        omega
    · simp at run
  case recclosure loc supplied cenv functions index =>
    cases hfound : functions[index]? with
    | none =>
      simp only [hfound] at run
      simp at run
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      simp only [hfound] at run ⊢
      split at run
      · rename_i valid
        split at run
        · simp at run
        · rename_i hfull
          simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
          obtain ⟨rfl, henv, hrest⟩ := run
          simp_all [destClosure, checkLoc, Bool.and_eq_true, decide_eq_true_eq,
            List.take_append_of_le_length, List.drop_append_of_le_length,
            List.reverse_append, List.reverse_reverse]
          omega
      · simp at run

/-- Applying the tail of a partial application's arguments directly to the
resulting partial closure gives the same result as applying both lists at once. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_partial_twice"]
theorem destClosure_partial_twice (maxApp : Nat) (f : Value) (args1 args2 : List Value)
    (cl : Value) (res : Option AppKind)
    (h : args1.length + args2.length ≤ maxApp ∧
      destClosure maxApp none f (args1 ++ args2) = res ∧
      destClosure maxApp none f args2 = some (.partialApp cl)) :
    destClosure maxApp none cl args1 = res := by
  obtain ⟨bound, run1, run2⟩ := h
  cases f
  all_goals simp only [destClosure] at run1 run2
  all_goals try contradiction
  case closure loc supplied env arity body =>
    simp only [List.length_append] at run1 run2
    split at run2
    · rename_i valid2
      split at run2
      · rename_i hpartial2
        simp only [Option.some.injEq, AppKind.partialApp.injEq] at run2
        subst cl
        have hsmall2 : supplied.length < arity := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid2
          exact valid2.2
        have hcond1 : (checkLoc maxApp none loc arity (args1.length + args2.length)
            supplied.length && decide (supplied.length < arity)) = true := by
          have hcheck1 : checkLoc maxApp none loc arity (args1.length + args2.length)
              supplied.length = true := by
            simp only [checkLoc, decide_eq_true_eq]
            omega
          simp [hcheck1, hsmall2]
        rw [if_pos hcond1] at run1
        split at run1
        · rename_i hpart
          rw [← run1]
          have hsmall' : args2.length + supplied.length < arity := by omega
          have hcheck' : checkLoc maxApp none loc arity args1.length
              (args2.length + supplied.length) = true := by
            simp only [checkLoc, decide_eq_true_eq]
            omega
          have hpart' : args1.length + (args2.length + supplied.length) < arity := by omega
          simp only [destClosure, List.length_append]
          rw [if_pos (by simp [hcheck', hsmall']), if_pos hpart']
          simp only [List.append_assoc]
        · rename_i hfull
          rw [← run1]
          have hsmall' : args2.length + supplied.length < arity := by omega
          have hcheck' : checkLoc maxApp none loc arity args1.length
              (args2.length + supplied.length) = true := by
            simp only [checkLoc, decide_eq_true_eq]
            omega
          have hpart' : ¬ args1.length + (args2.length + supplied.length) < arity := by omega
          have hk' : arity - (args2.length + supplied.length) =
              arity - supplied.length - args2.length := by omega
          have hdropEq : ((args1 ++ args2).reverse.drop (arity - supplied.length)).reverse
              = (args1.reverse.drop (arity - (args2.length + supplied.length))).reverse := by
            rw [List.reverse_append, List.drop_append]
            rw [List.drop_eq_nil_of_le (by
              simp only [List.length_reverse]
              omega)]
            rw [List.nil_append]
            simp only [List.length_reverse]
            rw [← hk']
          have htakeEq : ((args1 ++ args2).reverse.take (arity - supplied.length)).reverse.append
              (supplied ++ env)
              = (args1.reverse.take (arity - (args2.length + supplied.length))).reverse.append
                ((args2 ++ supplied) ++ env) := by
            rw [List.reverse_append, List.take_append]
            rw [List.take_of_length_le (by
              simp only [List.length_reverse]
              omega)]
            simp only [List.length_reverse]
            rw [← hk', List.reverse_append, List.reverse_reverse]
            show ((List.take (arity - (args2.length + supplied.length))
                args1.reverse).reverse ++ args2)
                ++ (supplied ++ env)
                = (List.take (arity - (args2.length + supplied.length))
                    args1.reverse).reverse ++ ((args2 ++ supplied) ++ env)
            simp only [List.append_assoc]
          simp only [destClosure, List.length_append]
          rw [if_pos (by simp [hcheck', hsmall']), if_neg hpart']
          rw [← htakeEq, ← hdropEq]
      · simp at run2
    · simp at run2
  case recclosure loc supplied env functions index =>
    cases hfound : functions[index]? with
    | none =>
      simp only [hfound] at run1 run2
      simp at run2
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      simp only [hfound] at run1 run2 ⊢
      simp only [List.length_append] at run1 run2
      split at run2
      · rename_i valid2
        split at run2
        · rename_i hpartial2
          simp only [Option.some.injEq, AppKind.partialApp.injEq] at run2
          subst cl
          have hsmall2 : supplied.length < arity := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid2
            exact valid2.2
          have hcond1 : (checkLoc maxApp none (loc.map (fun loc => 2 * index + loc)) arity
              (args1.length + args2.length) supplied.length &&
              decide (supplied.length < arity)) = true := by
            have hcheck1 : checkLoc maxApp none (loc.map (fun loc => 2 * index + loc)) arity
                (args1.length + args2.length) supplied.length = true := by
              simp only [checkLoc, decide_eq_true_eq]
              omega
            simp [hcheck1, hsmall2]
          rw [if_pos hcond1] at run1
          split at run1
          · rename_i hpart
            rw [← run1]
            have hsmall' : args2.length + supplied.length < arity := by omega
            have hcheck' : checkLoc maxApp none (loc.map (fun loc => 2 * index + loc)) arity
                args1.length (args2.length + supplied.length) = true := by
              simp only [checkLoc, decide_eq_true_eq]
              omega
            have hpart' : args1.length + (args2.length + supplied.length) < arity := by omega
            simp only [destClosure, hfound, List.length_append]
            rw [if_pos (by simp [hcheck', hsmall']), if_pos hpart']
            simp only [List.append_assoc]
          · rename_i hfull
            rw [← run1]
            have hsmall' : args2.length + supplied.length < arity := by omega
            have hcheck' : checkLoc maxApp none (loc.map (fun loc => 2 * index + loc)) arity
                args1.length (args2.length + supplied.length) = true := by
              simp only [checkLoc, decide_eq_true_eq]
              omega
            have hpart' : ¬ args1.length + (args2.length + supplied.length) < arity := by omega
            have hk' : arity - (args2.length + supplied.length) =
                arity - supplied.length - args2.length := by omega
            have hdropEq : ((args1 ++ args2).reverse.drop (arity - supplied.length)).reverse
                = (args1.reverse.drop (arity - (args2.length + supplied.length))).reverse := by
              rw [List.reverse_append, List.drop_append]
              rw [List.drop_eq_nil_of_le (by
                simp only [List.length_reverse]
                omega)]
              rw [List.nil_append]
              simp only [List.length_reverse]
              rw [← hk']
            have htakeEq : ((args1 ++ args2).reverse.take (arity - supplied.length)).reverse.append
                (supplied ++
                  List.map (fun i => Value.recclosure loc [] env functions i)
                    (List.range functions.length) ++ env)
                = (args1.reverse.take (arity - (args2.length + supplied.length))).reverse.append
                  (args2 ++ supplied ++
                    List.map (fun i => Value.recclosure loc [] env functions i)
                      (List.range functions.length) ++ env) := by
              rw [List.reverse_append, List.take_append]
              rw [List.take_of_length_le (by
                simp only [List.length_reverse]
                omega)]
              simp only [List.length_reverse]
              rw [← hk', List.reverse_append, List.reverse_reverse]
              show ((List.take (arity - (args2.length + supplied.length))
                  args1.reverse).reverse ++ args2)
                  ++ (supplied ++ List.map (fun i => Value.recclosure loc [] env functions i)
                    (List.range functions.length) ++ env)
                  = (List.take (arity - (args2.length + supplied.length))
                      args1.reverse).reverse
                    ++ (args2 ++ supplied ++
                      List.map (fun i => Value.recclosure loc [] env functions i)
                        (List.range functions.length) ++ env)
              simp only [List.append_assoc]
            simp only [destClosure, hfound, List.length_append]
            rw [if_pos (by simp [hcheck', hsmall']), if_neg hpart']
            rw [← htakeEq, ← hdropEq]
        · simp at run2
      · simp at run2

/-- Splitting a partial application's arguments: the dropped tail alone still
partially applies, and the full list's result is the kept prefix added on top. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_partial_split"]
theorem destClosure_partial_split (maxApp : Nat) (v1 : Value) (vs : List Value) (v2 : Value)
    (n : Nat)
    (h : destClosure maxApp none v1 vs = some (.partialApp v2) ∧ n ≤ vs.length) :
    ∃ v3, destClosure maxApp none v1 (vs.drop n) = some (.partialApp v3) ∧
      v2 = cloAddPartialArgs (vs.take n) v3 := by
  obtain ⟨run, hn⟩ := h
  cases v1
  all_goals simp only [destClosure] at run
  all_goals try contradiction
  case closure loc supplied env arity body =>
    split at run
    · rename_i valid
      split at run
      · rename_i hpartial
        simp only [Option.some.injEq, AppKind.partialApp.injEq] at run
        have hlen : vs.length + supplied.length < arity := by simpa using hpartial
        refine ⟨.closure loc (vs.drop n ++ supplied) env arity body, ?_, ?_⟩
        · have hsmall : supplied.length < arity := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            exact valid.2
          have hcheck : checkLoc maxApp none loc arity (vs.length - n) supplied.length = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc] at valid ⊢
            omega
          have hpart : (vs.drop n).length + supplied.length < arity := by
            simp only [List.length_drop]
            omega
          simp only [destClosure]
          rw [if_pos (by simp [hcheck, hsmall]), if_pos hpart]
        · rw [← run]
          simp only [cloAddPartialArgs]
          rw [← List.append_assoc, List.take_append_drop]
      · simp at run
    · simp at run
  case recclosure loc supplied env functions index =>
    cases hfound : functions[index]? with
    | none =>
      simp only [hfound] at run
      simp at run
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      simp only [hfound] at run ⊢
      split at run
      · rename_i valid
        split at run
        · rename_i hpartial
          simp only [Option.some.injEq, AppKind.partialApp.injEq] at run
          have hlen : vs.length + supplied.length < arity := by simpa using hpartial
          refine ⟨.recclosure loc (vs.drop n ++ supplied) env functions index, ?_, ?_⟩
          · have hsmall : supplied.length < arity := by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
              exact valid.2
            have hcheck : checkLoc maxApp none (loc.map (fun loc => 2 * index + loc)) arity
                (vs.length - n) supplied.length = true := by
              simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc] at valid ⊢
              omega
            have hpart : (vs.drop n).length + supplied.length < arity := by
              simp only [List.length_drop]
              omega
            simp only [destClosure, hfound]
            rw [if_pos (by simp [hcheck, hsmall]), if_pos hpart]
          · rw [← run]
            simp only [cloAddPartialArgs]
            rw [← List.append_assoc, List.take_append_drop]
        · simp at run
      · simp at run

/-- The prime form of `dest_closure_partial_split`: the kept prefix is the
result's tail and the dropped suffix is the argument list that still applies. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_partial_split'"]
theorem destClosure_partial_split_prime (maxApp n : Nat) (v : Value) (vs : List Value)
    (cl : Value)
    (h : destClosure maxApp none v vs = some (.partialApp cl) ∧ n ≤ vs.length) :
    ∃ cl0 used rest, vs = rest ++ used ∧ rest.length = n ∧
      destClosure maxApp none v used = some (.partialApp cl0) ∧
      cl = cloAddPartialArgs rest cl0 := by
  obtain ⟨v3, run, eq⟩ := destClosure_partial_split maxApp v vs cl n h
  refine ⟨v3, vs.drop n, vs.take n, ?_, ?_, run, eq⟩
  · exact (List.take_append_drop n vs).symm
  · rw [List.length_take, Nat.min_eq_left h.2]

/-- A full application that consumed its whole argument list leaves a partial
application of the suffix behind, which the prefix completes. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_NONE_Full_to_Partial"]
theorem destClosure_none_full_to_partial (maxApp : Nat) (v : Value) (l1 l2 : List Value)
    (b : ClosLang.Exp) (env : List Value)
    (h : destClosure maxApp none v (l1 ++ l2) = some (.fullApp b env []) ∧ l1 ≠ []) :
    ∃ cl, destClosure maxApp none v l2 = some (.partialApp cl) ∧
      destClosure maxApp none cl l1 = some (.fullApp b env []) := by
  obtain ⟨run, hne⟩ := h
  cases v
  all_goals simp only [destClosure] at run
  all_goals try contradiction
  case closure loc supplied env0 arity body =>
    split at run
    · rename_i valid
      split at run
      · simp at run
      · rename_i hfull
        simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
        obtain ⟨rfl, henv, hrest⟩ := run
        have hdrop : (l1 ++ l2).reverse.drop (arity - supplied.length) = [] := by
          have h := congrArg List.reverse hrest
          simpa using h
        have hk : l1.length + l2.length ≤ arity - supplied.length := by
          have := List.drop_eq_nil_iff.mp hdrop
          simp only [List.length_reverse, List.length_append] at this
          omega
        have hl1pos : 0 < l1.length := by
          cases l1 with
          | nil => exact absurd rfl hne
          | cons _ _ => simp
        have hsmall : supplied.length < arity := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          exact valid.2
        have hmax : l1.length + l2.length ≤ maxApp := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc, List.length_append] at valid
          omega
        refine ⟨.closure loc (l2 ++ supplied) env0 arity body, ?_, ?_⟩
        · have hcheck : checkLoc maxApp none loc arity l2.length supplied.length = true := by
            simp only [checkLoc, decide_eq_true_eq]
            omega
          have hpart : l2.length + supplied.length < arity := by omega
          simp only [destClosure]
          rw [if_pos (by simp [hcheck, hsmall]), if_pos hpart]
        · have hsmall' : l2.length + supplied.length < arity := by omega
          have hcheck' : checkLoc maxApp none loc arity l1.length
              (l2.length + supplied.length) = true := by
            simp only [checkLoc, decide_eq_true_eq]
            omega
          have hfull' : ¬ l1.length + (l2.length + supplied.length) < arity := by
            simp only [List.length_append] at hfull
            omega
          have htake : (l1 ++ l2).reverse.take (arity - supplied.length) = (l1 ++ l2).reverse := by
            rw [List.take_of_length_le]
            simp only [List.length_reverse, List.length_append]
            omega
          have htake' : l1.reverse.take (arity - (l2.length + supplied.length)) = l1.reverse := by
            rw [List.take_of_length_le]
            simp only [List.length_reverse]
            omega
          have hdrop' : l1.reverse.drop (arity - (l2.length + supplied.length)) = [] := by
            rw [List.drop_eq_nil_of_le]
            simp only [List.length_reverse]
            omega
          have hswap : l1.reverse.reverse.append ((l2 ++ supplied) ++ env0)
              = (l1 ++ l2).reverse.reverse.append (supplied ++ env0) := by
            simp only [List.reverse_reverse, List.reverse_append]
            show l1 ++ ((l2 ++ supplied) ++ env0) = (l1 ++ l2) ++ (supplied ++ env0)
            simp only [List.append_assoc]
          simp only [destClosure, List.length_append]
          rw [if_pos (by simp [hcheck', hsmall']), if_neg hfull']
          rw [htake', hdrop', ← henv, htake, hswap]
          simp
    · simp at run
  case recclosure loc supplied env0 functions index =>
    cases hfound : functions[index]? with
    | none =>
      simp only [hfound] at run
      simp at run
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      simp only [hfound] at run ⊢
      split at run
      · rename_i valid
        split at run
        · simp at run
        · rename_i hfull
          simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
          obtain ⟨rfl, henv, hrest⟩ := run
          have hdrop : (l1 ++ l2).reverse.drop (arity - supplied.length) = [] := by
            have h := congrArg List.reverse hrest
            simpa using h
          have hk : l1.length + l2.length ≤ arity - supplied.length := by
            have := List.drop_eq_nil_iff.mp hdrop
            simp only [List.length_reverse, List.length_append] at this
            omega
          have hl1pos : 0 < l1.length := by
            cases l1 with
            | nil => exact absurd rfl hne
            | cons _ _ => simp
          have hsmall : supplied.length < arity := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            exact valid.2
          have hmax : l1.length + l2.length ≤ maxApp := by
            simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc, List.length_append] at valid
            omega
          refine ⟨.recclosure loc (l2 ++ supplied) env0 functions index, ?_, ?_⟩
          · have hcheck : checkLoc maxApp none (loc.map (fun loc => 2 * index + loc)) arity
                l2.length supplied.length = true := by
              simp only [checkLoc, decide_eq_true_eq]
              omega
            have hpart : l2.length + supplied.length < arity := by omega
            simp only [destClosure, hfound]
            rw [if_pos (by simp [hcheck, hsmall]), if_pos hpart]
          · have hsmall' : l2.length + supplied.length < arity := by omega
            have hcheck' : checkLoc maxApp none (loc.map (fun loc => 2 * index + loc)) arity
                l1.length (l2.length + supplied.length) = true := by
              simp only [checkLoc, decide_eq_true_eq]
              omega
            have hfull' : ¬ l1.length + (l2.length + supplied.length) < arity := by
              simp only [List.length_append] at hfull
              omega
            have htake : (l1 ++ l2).reverse.take (arity - supplied.length) =
                (l1 ++ l2).reverse := by
              rw [List.take_of_length_le]
              simp only [List.length_reverse, List.length_append]
              omega
            have htake' : l1.reverse.take (arity - (l2.length + supplied.length)) = l1.reverse := by
              rw [List.take_of_length_le]
              simp only [List.length_reverse]
              omega
            have hdrop' : l1.reverse.drop (arity - (l2.length + supplied.length)) = [] := by
              rw [List.drop_eq_nil_of_le]
              simp only [List.length_reverse]
              omega
            have hswap : l1.reverse.reverse.append
                (l2 ++ supplied ++
                  List.map (fun i => Value.recclosure loc [] env0 functions i)
                    (List.range functions.length) ++ env0)
                = (l1 ++ l2).reverse.reverse.append
                  (supplied ++
                    List.map (fun i => Value.recclosure loc [] env0 functions i)
                      (List.range functions.length) ++ env0) := by
              simp only [List.reverse_reverse, List.reverse_append]
              show l1 ++
                  ((l2 ++ supplied ++
                    List.map (fun i => Value.recclosure loc [] env0 functions i)
                      (List.range functions.length)) ++ env0)
                  = (l1 ++ l2) ++
                    ((supplied ++
                      List.map (fun i => Value.recclosure loc [] env0 functions i)
                        (List.range functions.length)) ++ env0)
              simp only [List.append_assoc]
            simp only [destClosure, hfound, List.length_append]
            rw [if_pos (by simp [hcheck', hsmall']), if_neg hfull']
            rw [htake', hdrop', ← henv, htake, hswap]
            simp
      · simp at run

/-- A full application can be staged: its remainder plus a further application of
that remainder completes it. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dest_closure_full_split'"]
theorem destClosure_full_split_prime (maxApp : Nat) (loc : Option Nat) (v : Value)
    (vs : List Value) (e : ClosLang.Exp) (env rest : List Value)
    (run : destClosure maxApp loc v vs = some (.fullApp e env rest)) :
    ∃ used, vs = rest ++ used ∧ destClosure maxApp loc v used = some (.fullApp e env []) := by
  cases v
  all_goals simp only [destClosure] at run
  all_goals try contradiction
  case closure loc0 supplied env0 arity body =>
    split at run
    · rename_i valid
      split at run
      · simp at run
      · rename_i hfull
        simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
        obtain ⟨rfl, henv, hrest⟩ := run
        refine ⟨(vs.reverse.take (arity - supplied.length)).reverse, ?_, ?_⟩
        · have h := congrArg List.reverse
            (List.take_append_drop (arity - supplied.length) vs.reverse)
          simp only [List.reverse_append, List.reverse_reverse] at h
          rw [← hrest]
          exact h.symm
        · have hsmall : supplied.length < arity := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            exact valid.2
          have hlenUsed : (vs.reverse.take (arity - supplied.length)).length =
              arity - supplied.length := by
            rw [List.length_take, List.length_reverse]
            omega
          have hcheck : checkLoc maxApp loc loc0 arity
              (min (arity - supplied.length) vs.length) supplied.length = true := by
            cases loc with
            | none =>
              simp only [checkLoc, decide_eq_true_eq]
              simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc] at valid
              exact le_trans (Nat.min_le_right _ _) valid.1
            | some a =>
              simp only [checkLoc, decide_eq_true_eq]
              simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc] at valid
              obtain ⟨⟨har, hzero, hloc⟩, _⟩ := valid
              refine ⟨?_, hzero, hloc⟩
              rw [Nat.min_eq_left (by omega), hzero, Nat.sub_zero]
          have hfull' : ¬ (min (arity - supplied.length) vs.length + supplied.length < arity) := by
            rw [Nat.min_eq_left (by omega)]
            omega
          have htakeUsed : (vs.reverse.take (arity - supplied.length)).reverse.reverse.take
              (arity - supplied.length) = vs.reverse.take (arity - supplied.length) := by
            rw [List.reverse_reverse, List.take_take, Nat.min_self]
          have hdropUsed : (vs.reverse.take (arity - supplied.length)).reverse.reverse.drop
              (arity - supplied.length) = [] := by
            rw [List.reverse_reverse]
            exact List.drop_eq_nil_of_le (by
              rw [List.length_take, List.length_reverse]
              omega)
          simp only [destClosure, List.length_reverse, List.length_take]
          rw [if_pos (by simp [hcheck, hsmall]), if_neg hfull', ← henv, htakeUsed, hdropUsed]
          simp
    · simp at run
  case recclosure loc0 supplied env0 functions index =>
    cases hfound : functions[index]? with
    | none =>
      simp only [hfound] at run
      simp at run
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      simp only [hfound] at run ⊢
      split at run
      · rename_i valid
        split at run
        · simp at run
        · rename_i hfull
          simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
          obtain ⟨rfl, henv, hrest⟩ := run
          refine ⟨(vs.reverse.take (arity - supplied.length)).reverse, ?_, ?_⟩
          · have h := congrArg List.reverse
              (List.take_append_drop (arity - supplied.length) vs.reverse)
            simp only [List.reverse_append, List.reverse_reverse] at h
            rw [← hrest]
            exact h.symm
          · have hsmall : supplied.length < arity := by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
              exact valid.2
            have hlenUsed : (vs.reverse.take (arity - supplied.length)).length =
                arity - supplied.length := by
              rw [List.length_take, List.length_reverse]
              omega
            have hcheck : checkLoc maxApp loc
                (loc0.map (fun l => 2 * index + l)) arity
                (min (arity - supplied.length) vs.length) supplied.length = true := by
              cases loc with
              | none =>
                simp only [checkLoc, decide_eq_true_eq]
                simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc] at valid
                exact le_trans (Nat.min_le_right _ _) valid.1
              | some a =>
                simp only [checkLoc, decide_eq_true_eq]
                simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc] at valid
                obtain ⟨⟨har, hzero, hloc⟩, _⟩ := valid
                refine ⟨?_, hzero, hloc⟩
                rw [Nat.min_eq_left (by omega), hzero, Nat.sub_zero]
            have hfull' : ¬ (min (arity - supplied.length) vs.length +
                supplied.length < arity) := by
              rw [Nat.min_eq_left (by omega)]
              omega
            have htakeUsed : (vs.reverse.take (arity - supplied.length)).reverse.reverse.take
                (arity - supplied.length) = vs.reverse.take (arity - supplied.length) := by
              rw [List.reverse_reverse, List.take_take, Nat.min_self]
            have hdropUsed : (vs.reverse.take (arity - supplied.length)).reverse.reverse.drop
                (arity - supplied.length) = [] := by
              rw [List.reverse_reverse]
              exact List.drop_eq_nil_of_le (by
                rw [List.length_take, List.length_reverse]
                omega)
            simp only [destClosure, hfound, List.length_reverse, List.length_take]
            rw [if_pos (by simp [hcheck, hsmall]), if_neg hfull', ← henv, htakeUsed, hdropUsed]
            simp
      · simp at run

end Flapjack.Compiler.Backend.ClosProps
