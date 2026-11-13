module

public import Flapjack.Misc.Option.MapM
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.Syntactic
public import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
public import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMtiSyntactic
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

@[expose] public section

/-! Syntactic invariants needed by the pass after multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang ClosProps

/-- Collecting function arguments preserves absence of label operations. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_args_no_Labels"]
theorem collectArgs_noLabels (maxApp count : Nat) (expression : Exp) (arity : Nat) (body : Exp)
    (premises : collectArgs maxApp count expression = (arity, body) ∧ noLabels expression) :
    noLabels body := by
  obtain ⟨run, valid⟩ := premises
  cases expression with
  | fn name location vars n inner =>
    cases location with
    | some location =>
      simp only [collectArgs, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact valid
    | none =>
      cases vars with
      | some vars =>
        simp only [collectArgs, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        exact valid
      | none =>
        simp only [collectArgs] at run
        split at run
        · exact collectArgs_noLabels maxApp (count + n) inner arity body ⟨run, by simpa [noLabels] using valid⟩
        · cases run
          exact valid
  | _ => simp only [collectArgs, Prod.mk.injEq] at run; obtain ⟨rfl, rfl⟩ := run; exact valid
termination_by sizeOf expression

/-- Collecting applications preserves absence of label operations. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_apps_no_Labels"]
theorem collectApps_noLabels (maxApp : Nat) (args : List Exp) (expression : Exp)
    (collected : List Exp) (head : Exp)
    (premises : collectApps maxApp args expression = (collected, head) ∧
      (∀ e ∈ args, noLabels e) ∧ noLabels expression) :
    (∀ e ∈ collected, noLabels e) ∧ noLabels head := by
  revert collected head
  fun_induction collectApps maxApp args expression <;> simp_all
  case case1 =>
    rename_i ih
    intro collected head hr argsValid valid
    simp only [noLabels] at valid
    refine ih collected head hr (fun e member => ?_) valid.1
    rcases member with h | h
    · exact argsValid e h
    · exact (noLabelsList_iff _).mp valid.2 e h

/-- Flapjack projection form of `every_Fn_vs_NONE_collect_args`, used by the
recursive traversal proof. -/
theorem collectArgs_varsNone (maxApp count : Nat) (expression : Exp) :
    fnVarsNoneExp expression ↔ fnVarsNoneExp (collectArgs maxApp count expression).2 := by
  cases expression with
  | fn name location vars arity body =>
    cases location with
    | some location => simp [collectArgs]
    | none =>
      cases vars with
      | some vars => simp [collectArgs]
      | none =>
        simp only [collectArgs]
        split
        · simpa [fnVarsNoneExp] using collectArgs_varsNone maxApp (count + arity) body
        · simp
  | _ => simp [collectArgs]
termination_by sizeOf expression

/-- Flapjack projection form of `every_Fn_vs_NONE_collect_apps`, used by the
recursive traversal proof. -/
theorem collectApps_varsNone (maxApp : Nat) (args : List Exp) (expression : Exp) :
    (everyFnVarsNone args ∧ fnVarsNoneExp expression) ↔
      (everyFnVarsNone (collectApps maxApp args expression).1 ∧
        fnVarsNoneExp (collectApps maxApp args expression).2) := by
  have append (xs ys : List Exp) : everyFnVarsNone (xs ++ ys) ↔
      everyFnVarsNone xs ∧ everyFnVarsNone ys := by
    induction xs with
    | nil => simp [everyFnVarsNone]
    | cons x xs ih => simp [everyFnVarsNone, ih, and_assoc]
  cases expression with
  | app trace location head more =>
    cases location with
    | some location => simp [collectApps]
    | none =>
      simp only [collectApps]
      split
      · have ih := collectApps_varsNone maxApp (args ++ more) head
        simp only [append] at ih
        simpa [fnVarsNoneExp, and_assoc, and_left_comm, and_comm] using ih
      · simp
  | _ => simp [collectApps]
termination_by sizeOf expression

/-- Argument collection preserves the singleton annotation predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "every_Fn_vs_NONE_collect_args"]
theorem everyFnVarsNone_collectArgs (maxApp count : Nat) (expression : Exp)
    (arity : Nat) (body : Exp) (run : collectArgs maxApp count expression = (arity, body)) :
    everyFnVarsNone [body] ↔ everyFnVarsNone [expression] := by
  have invariant := collectArgs_varsNone maxApp count expression
  rw [run] at invariant
  simpa [everyFnVarsNone] using invariant.symm

/-- Application collection preserves the annotation predicate on both parts. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "every_Fn_vs_NONE_collect_apps"]
theorem everyFnVarsNone_collectApps (maxApp : Nat) (args : List Exp) (expression : Exp)
    (collected : List Exp) (head : Exp) (run : collectApps maxApp args expression = (collected, head)) :
    (everyFnVarsNone collected ∧ everyFnVarsNone [head]) ↔
      (everyFnVarsNone args ∧ everyFnVarsNone [expression]) := by
  have invariant := collectApps_varsNone maxApp args expression
  rw [run] at invariant
  simpa [everyFnVarsNone] using invariant.symm

/-- Flapjack projection form of `contains_App_SOME_collect_args`, used by the
recursive traversal proof. -/
theorem collectArgs_containsAppSome (maxApp count : Nat) (expression : Exp) :
    containsAppSomeExp maxApp expression ↔
      containsAppSomeExp maxApp (collectArgs maxApp count expression).2 := by
  cases expression with
  | fn name location vars arity body =>
    cases location with
    | some location => simp [collectArgs]
    | none =>
      cases vars with
      | some vars => simp [collectArgs]
      | none =>
        simp only [collectArgs]
        split
        · simpa [containsAppSomeExp] using collectArgs_containsAppSome maxApp (count + arity) body
        · simp
  | _ => simp [collectArgs]
termination_by sizeOf expression

/-- Flapjack projection form of `contains_App_SOME_collect_apps`, used by the
recursive traversal proof. -/
theorem collectApps_containsAppSome (maxApp : Nat) (args : List Exp) (expression : Exp) :
    (maxApp < args.length ∨ containsAppSome maxApp args ∨ containsAppSomeExp maxApp expression) ↔
      (maxApp < (collectApps maxApp args expression).1.length ∨
        containsAppSome maxApp (collectApps maxApp args expression).1 ∨
        containsAppSomeExp maxApp (collectApps maxApp args expression).2) := by
  cases expression with
  | app trace location head more =>
    cases location with
    | some location => simp [collectApps]
    | none =>
      simp only [collectApps]
      by_cases fits : args.length + more.length ≤ maxApp
      · simp only [fits, ite_true]
        have ih := collectApps_containsAppSome maxApp (args ++ more) head
        simp only [List.length_append, Flapjack.Compiler.Backend.FlatToClos.containsAppSomeAppend] at ih
        simp only [containsAppSomeExp, Option.isSome_none, Bool.false_eq_true, false_or]
        have argsSmall : ¬ maxApp < args.length := by omega
        have moreSmall : ¬ maxApp < more.length := by omega
        have sumSmall : ¬ maxApp < args.length + more.length := by omega
        simp only [argsSmall, moreSmall, sumSmall, false_or] at ih ⊢
        simpa [or_assoc, or_left_comm, or_comm] using ih
      · simp [fits]
  | _ => simp [collectApps]
termination_by sizeOf expression

/-- Argument collection preserves the singleton application predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "contains_App_SOME_collect_args"]
theorem containsAppSome_collectArgs (maxApp count : Nat) (expression : Exp)
    (arity : Nat) (body : Exp) (run : collectArgs maxApp count expression = (arity, body)) :
    containsAppSome maxApp [expression] ↔ containsAppSome maxApp [body] := by
  have invariant := collectArgs_containsAppSome maxApp count expression
  rw [run] at invariant
  simpa [containsAppSome] using invariant

/-- Application collection preserves the complete application predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "contains_App_SOME_collect_apps"]
theorem containsAppSome_collectApps (maxApp : Nat) (args : List Exp) (expression : Exp)
    (collected : List Exp) (head : Exp) (run : collectApps maxApp args expression = (collected, head)) :
    (maxApp < args.length ∨ containsAppSome maxApp args ∨ containsAppSome maxApp [expression]) ↔
      (maxApp < collected.length ∨ containsAppSome maxApp collected ∨ containsAppSome maxApp [head]) := by
  have invariant := collectApps_containsAppSome maxApp args expression
  rw [run] at invariant
  simpa [containsAppSome] using invariant

/-- A pointwise traversal that preserves application safety also preserves it
over the complete list. -/
private theorem mapM_containsAppSome (maxApp : Nat) (f : Exp → Option Exp) (source target : List Exp)
    (pointwise : ∀ e result, f e = some result →
      (containsAppSomeExp maxApp e ↔ containsAppSomeExp maxApp result))
    (run : source.mapM f = some target) :
    containsAppSome maxApp source ↔ containsAppSome maxApp target := by
  have rel := mapM_rel f (fun e result => containsAppSomeExp maxApp e ↔ containsAppSomeExp maxApp result) pointwise source target run
  clear run
  induction rel with
  | nil => rfl
  | cons first rest ih => simp only [containsAppSome, first, ih]

/-- The corresponding traversal property for recursive function bundles. -/
private theorem mapM_funs_containsAppSome (maxApp : Nat) (f : Nat × Exp → Option (Nat × Exp))
    (source target : List (Nat × Exp))
    (pointwise : ∀ entry result, f entry = some result →
      (containsAppSomeExp maxApp entry.2 ↔ containsAppSomeExp maxApp result.2))
    (run : source.mapM f = some target) :
    containsAppSomeFuns maxApp source ↔ containsAppSomeFuns maxApp target := by
  have rel := mapM_rel f (fun entry result => containsAppSomeExp maxApp entry.2 ↔ containsAppSomeExp maxApp result.2) pointwise source target run
  clear run
  induction rel with
  | nil => rfl
  | @cons a b xs ys first rest ih =>
    cases a
    cases b
    simp only [containsAppSomeFuns, first, ih]

/-- Every successful executable traversal preserves application safety. -/
theorem introMultiFuel_containsAppSome (fuel maxApp : Nat) (expression result : Exp)
    (run : introMultiFuel fuel maxApp expression = some result) :
    containsAppSomeExp maxApp expression ↔ containsAppSomeExp maxApp result := by
  induction fuel generalizing expression result with
  | zero => simp [introMultiFuel] at run
  | succ fuel ih =>
    have listStep (source target : List Exp)
        (run : source.mapM (introMultiFuel fuel maxApp) = some target) :
        containsAppSome maxApp source ↔ containsAppSome maxApp target :=
      mapM_containsAppSome maxApp _ source target (fun e result run => ih e result run) run
    cases expression with
    | var trace index => simp [introMultiFuel] at run; subst result; rfl
    | raise trace body =>
      cases step : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, step] at run
      | some next =>
        have equal : .raise trace next = result := by simpa [introMultiFuel, step] using run
        subst result
        simpa [containsAppSomeExp] using ih body next step
    | tick trace body =>
      cases step : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, step] at run
      | some next =>
        have equal : .tick trace next = result := by simpa [introMultiFuel, step] using run
        subst result
        simpa [containsAppSomeExp] using ih body next step
    | ifThenElse trace condition yes no =>
      cases hc : introMultiFuel fuel maxApp condition with
      | none => simp [introMultiFuel, hc] at run
      | some condition' =>
        cases hy : introMultiFuel fuel maxApp yes with
        | none => simp [introMultiFuel, hc, hy] at run
        | some yes' =>
          cases hn : introMultiFuel fuel maxApp no with
          | none => simp [introMultiFuel, hc, hy, hn] at run
          | some no' =>
            have equal : .ifThenElse trace condition' yes' no' = result := by
              simpa [introMultiFuel, hc, hy, hn] using run
            subst result
            simp only [containsAppSomeExp, ih condition condition' hc, ih yes yes' hy, ih no no' hn]
    | handle trace body handler =>
      cases hb : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, hb] at run
      | some body' =>
        cases hh : introMultiFuel fuel maxApp handler with
        | none => simp [introMultiFuel, hb, hh] at run
        | some handler' =>
          have equal : .handle trace body' handler' = result := by simpa [introMultiFuel, hb, hh] using run
          subst result
          simp only [containsAppSomeExp, ih body body' hb, ih handler handler' hh]
    | «let» trace bindings body =>
      cases hs : bindings.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some bindings' =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hs, hb] at run
        | some body' =>
          have equal : .let trace bindings' body' = result := by simpa [introMultiFuel, hs, hb] using run
          subst result
          simp only [containsAppSomeExp, ih body body' hb, listStep bindings bindings' hs]
    | call trace ticks location args =>
      cases hs : args.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some args' =>
        have equal : .call trace ticks location args' = result := by simpa [introMultiFuel, hs] using run
        subst result
        simpa [containsAppSomeExp] using listStep args args' hs
    | op trace op args =>
      cases hs : args.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some args' =>
        have equal : .op trace op args' = result := by simpa [introMultiFuel, hs] using run
        subst result
        cases op <;> try (simp [containsAppSomeExp, listStep args args' hs])
        case thunkOp operation => cases operation <;> simp [containsAppSomeExp, listStep args args' hs]
    | app trace location head args =>
      cases location with
      | some location =>
        cases hh : introMultiFuel fuel maxApp head with
        | none => simp [introMultiFuel, hh] at run
        | some head' =>
          cases ha : args.mapM (introMultiFuel fuel maxApp) with
          | none => simp [introMultiFuel, hh, ha] at run
          | some args' =>
            have equal : .app trace (some location) head' args' = result := by
              simpa [introMultiFuel, hh, ha] using run
            subst result
            simp [containsAppSomeExp]
      | none =>
        cases collected : collectApps maxApp args head with
        | mk collectedArgs collectedHead =>
          cases hh : introMultiFuel fuel maxApp collectedHead with
          | none => simp [introMultiFuel, collected, hh] at run
          | some head' =>
            cases ha : collectedArgs.mapM (introMultiFuel fuel maxApp) with
            | none => simp [introMultiFuel, collected, hh, ha] at run
            | some args' =>
              have equal : .app trace none head' args' = result := by
                simpa [introMultiFuel, collected, hh, ha] using run
              subst result
              have collector := collectApps_containsAppSome maxApp args head
              rw [collected] at collector
              simp only at collector
              have lengths := mapM_length collectedArgs (introMultiFuel fuel maxApp) args' ha
              simp only [containsAppSomeExp, Option.isSome_none, Bool.false_eq_true, false_or,
                ← ih collectedHead head' hh, ← listStep collectedArgs args' ha, lengths]
              simpa [or_assoc, or_left_comm, or_comm] using collector
    | fn name location vars arity body =>
      cases location with
      | some location =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => cases vars <;> simp [introMultiFuel, hb] at run
        | some body' =>
          cases vars <;> simp [introMultiFuel, hb] at run <;> subst result <;>
            simpa [containsAppSomeExp] using ih body body' hb
      | none =>
        cases vars with
        | some vars =>
          cases hb : introMultiFuel fuel maxApp body with
          | none => simp [introMultiFuel, hb] at run
          | some body' =>
            have equal : .fn name none (some vars) arity body' = result := by
              simpa [introMultiFuel, hb] using run
            subst result
            simpa [containsAppSomeExp] using ih body body' hb
        | none =>
          cases collected : collectArgs maxApp arity body with
          | mk count remaining =>
            cases hb : introMultiFuel fuel maxApp remaining with
            | none => simp [introMultiFuel, collected, hb] at run
            | some body' =>
              have equal : .fn name none none count body' = result := by
                simpa [introMultiFuel, collected, hb] using run
              subst result
              have collector := collectArgs_containsAppSome maxApp arity body
              rw [collected] at collector
              simpa [containsAppSomeExp, ih remaining body' hb] using collector
    | letrec names location vars functions body =>
      let collected (entry : Nat × Exp) : Option (Nat × Exp) := do
        let (arity, rest) := collectArgs maxApp entry.1 entry.2
        pure (arity, ← introMultiFuel fuel maxApp rest)
      have collectedStep : ∀ target, functions.mapM collected = some target →
          (containsAppSomeFuns maxApp functions ↔ containsAppSomeFuns maxApp target) := by
        intro target run
        apply mapM_funs_containsAppSome maxApp collected functions target _ run
        intro entry result run
        cases entry with
        | mk arity body =>
          cases found : collectArgs maxApp arity body with
          | mk count rest =>
            cases step : introMultiFuel fuel maxApp rest with
            | none => simp [collected, found, step] at run
            | some body' =>
              have equal : (count, body') = result := by simpa [collected, found, step] using run
              subst result
              have collector := collectArgs_containsAppSome maxApp arity body
              rw [found] at collector
              exact collector.trans (ih rest body' step)
      cases location <;> cases vars
      case none.none =>
        change (do
          let fs ← functions.mapM collected
          let b ← introMultiFuel fuel maxApp body
          pure (.letrec names none none fs b)) = some result at run
        cases hf : functions.mapM collected with
        | none => simp [hf] at run
        | some functions' =>
          cases hb : introMultiFuel fuel maxApp body with
          | none => simp [hf, hb] at run
          | some body' =>
            simp [hf, hb] at run
            subst result
            simp only [containsAppSomeExp, collectedStep functions' hf, ih body body' hb]
      all_goals
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hb] at run
        | some body' =>
          simp [introMultiFuel, hb] at run
          subst result
          simp only [containsAppSomeExp, ih body body' hb]

/-- A pointwise traversal that preserves absence of captured-variable annotations also preserves it
over the complete list. -/
private theorem mapM_varsNone (f : Exp → Option Exp) (source target : List Exp)
    (pointwise : ∀ e result, f e = some result →
      (fnVarsNoneExp e ↔ fnVarsNoneExp result))
    (run : source.mapM f = some target) :
    everyFnVarsNone source ↔ everyFnVarsNone target := by
  have rel := mapM_rel f (fun e result => fnVarsNoneExp e ↔ fnVarsNoneExp result) pointwise source target run
  clear run
  induction rel with
  | nil => rfl
  | cons first rest ih => simp only [everyFnVarsNone, first, ih]

/-- The corresponding traversal property for recursive function bundles. -/
private theorem mapM_funs_varsNone (f : Nat × Exp → Option (Nat × Exp))
    (source target : List (Nat × Exp))
    (pointwise : ∀ entry result, f entry = some result →
      (fnVarsNoneExp entry.2 ↔ fnVarsNoneExp result.2))
    (run : source.mapM f = some target) :
    fnVarsNoneFuns source ↔ fnVarsNoneFuns target := by
  have rel := mapM_rel f (fun entry result => fnVarsNoneExp entry.2 ↔ fnVarsNoneExp result.2) pointwise source target run
  clear run
  induction rel with
  | nil => rfl
  | @cons a b xs ys first rest ih =>
    cases a
    cases b
    simp only [fnVarsNoneFuns, first, ih]

/-- Every successful executable traversal preserves absence of captured-variable annotations. -/
theorem introMultiFuel_varsNone (fuel maxApp : Nat) (expression result : Exp)
    (run : introMultiFuel fuel maxApp expression = some result) :
    fnVarsNoneExp expression ↔ fnVarsNoneExp result := by
  induction fuel generalizing expression result with
  | zero => simp [introMultiFuel] at run
  | succ fuel ih =>
    have listStep (source target : List Exp)
        (run : source.mapM (introMultiFuel fuel maxApp) = some target) :
        everyFnVarsNone source ↔ everyFnVarsNone target :=
      mapM_varsNone _ source target (fun e result run => ih e result run) run
    cases expression with
    | var trace index => simp [introMultiFuel] at run; subst result; rfl
    | raise trace body =>
      cases step : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, step] at run
      | some next =>
        have equal : .raise trace next = result := by simpa [introMultiFuel, step] using run
        subst result
        simpa [fnVarsNoneExp] using ih body next step
    | tick trace body =>
      cases step : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, step] at run
      | some next =>
        have equal : .tick trace next = result := by simpa [introMultiFuel, step] using run
        subst result
        simpa [fnVarsNoneExp] using ih body next step
    | ifThenElse trace condition yes no =>
      cases hc : introMultiFuel fuel maxApp condition with
      | none => simp [introMultiFuel, hc] at run
      | some condition' =>
        cases hy : introMultiFuel fuel maxApp yes with
        | none => simp [introMultiFuel, hc, hy] at run
        | some yes' =>
          cases hn : introMultiFuel fuel maxApp no with
          | none => simp [introMultiFuel, hc, hy, hn] at run
          | some no' =>
            have equal : .ifThenElse trace condition' yes' no' = result := by
              simpa [introMultiFuel, hc, hy, hn] using run
            subst result
            simp only [fnVarsNoneExp, ih condition condition' hc, ih yes yes' hy, ih no no' hn]
    | handle trace body handler =>
      cases hb : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, hb] at run
      | some body' =>
        cases hh : introMultiFuel fuel maxApp handler with
        | none => simp [introMultiFuel, hb, hh] at run
        | some handler' =>
          have equal : .handle trace body' handler' = result := by simpa [introMultiFuel, hb, hh] using run
          subst result
          simp only [fnVarsNoneExp, ih body body' hb, ih handler handler' hh]
    | «let» trace bindings body =>
      cases hs : bindings.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some bindings' =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hs, hb] at run
        | some body' =>
          have equal : .let trace bindings' body' = result := by simpa [introMultiFuel, hs, hb] using run
          subst result
          simp only [fnVarsNoneExp, ih body body' hb, listStep bindings bindings' hs]
    | call trace ticks location args =>
      cases hs : args.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some args' =>
        have equal : .call trace ticks location args' = result := by simpa [introMultiFuel, hs] using run
        subst result
        simpa [fnVarsNoneExp] using listStep args args' hs
    | op trace op args =>
      cases hs : args.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some args' =>
        have equal : .op trace op args' = result := by simpa [introMultiFuel, hs] using run
        subst result
        simpa [fnVarsNoneExp] using listStep args args' hs
    | app trace location head args =>
      cases location with
      | some location =>
        cases hh : introMultiFuel fuel maxApp head with
        | none => simp [introMultiFuel, hh] at run
        | some head' =>
          cases ha : args.mapM (introMultiFuel fuel maxApp) with
          | none => simp [introMultiFuel, hh, ha] at run
          | some args' =>
            have equal : .app trace (some location) head' args' = result := by
              simpa [introMultiFuel, hh, ha] using run
            subst result
            simp [fnVarsNoneExp, ih head head' hh, listStep args args' ha]
      | none =>
        cases collected : collectApps maxApp args head with
        | mk collectedArgs collectedHead =>
          cases hh : introMultiFuel fuel maxApp collectedHead with
          | none => simp [introMultiFuel, collected, hh] at run
          | some head' =>
            cases ha : collectedArgs.mapM (introMultiFuel fuel maxApp) with
            | none => simp [introMultiFuel, collected, hh, ha] at run
            | some args' =>
              have equal : .app trace none head' args' = result := by
                simpa [introMultiFuel, collected, hh, ha] using run
              subst result
              have collector := collectApps_varsNone maxApp args head
              rw [collected] at collector
              simp only at collector
              simp only [fnVarsNoneExp, ← ih collectedHead head' hh, ← listStep collectedArgs args' ha]
              simpa [and_comm] using collector
    | fn name location vars arity body =>
      cases location with
      | some location =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => cases vars <;> simp [introMultiFuel, hb] at run
        | some body' =>
          cases vars <;> simp [introMultiFuel, hb] at run <;> subst result <;>
            simp [fnVarsNoneExp, ih body body' hb]
      | none =>
        cases vars with
        | some vars =>
          cases hb : introMultiFuel fuel maxApp body with
          | none => simp [introMultiFuel, hb] at run
          | some body' =>
            have equal : .fn name none (some vars) arity body' = result := by
              simpa [introMultiFuel, hb] using run
            subst result
            simp [fnVarsNoneExp]
        | none =>
          cases collected : collectArgs maxApp arity body with
          | mk count remaining =>
            cases hb : introMultiFuel fuel maxApp remaining with
            | none => simp [introMultiFuel, collected, hb] at run
            | some body' =>
              have equal : .fn name none none count body' = result := by
                simpa [introMultiFuel, collected, hb] using run
              subst result
              have collector := collectArgs_varsNone maxApp arity body
              rw [collected] at collector
              simpa [fnVarsNoneExp, ih remaining body' hb] using collector
    | letrec names location vars functions body =>
      let collected (entry : Nat × Exp) : Option (Nat × Exp) := do
        let (arity, rest) := collectArgs maxApp entry.1 entry.2
        pure (arity, ← introMultiFuel fuel maxApp rest)
      have collectedStep : ∀ target, functions.mapM collected = some target →
          (fnVarsNoneFuns functions ↔ fnVarsNoneFuns target) := by
        intro target run
        apply mapM_funs_varsNone collected functions target _ run
        intro entry result run
        cases entry with
        | mk arity body =>
          cases found : collectArgs maxApp arity body with
          | mk count rest =>
            cases step : introMultiFuel fuel maxApp rest with
            | none => simp [collected, found, step] at run
            | some body' =>
              have equal : (count, body') = result := by simpa [collected, found, step] using run
              subst result
              have collector := collectArgs_varsNone maxApp arity body
              rw [found] at collector
              exact collector.trans (ih rest body' step)
      cases location <;> cases vars
      case none.none =>
        change (do
          let fs ← functions.mapM collected
          let b ← introMultiFuel fuel maxApp body
          pure (.letrec names none none fs b)) = some result at run
        cases hf : functions.mapM collected with
        | none => simp [hf] at run
        | some functions' =>
          cases hb : introMultiFuel fuel maxApp body with
          | none => simp [hf, hb] at run
          | some body' =>
            simp [hf, hb] at run
            subst result
            simp only [fnVarsNoneExp, collectedStep functions' hf, ih body body' hb]
      all_goals
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hb] at run
        | some body' =>
          simp [introMultiFuel, hb] at run
          subst result
          simp only [fnVarsNoneExp, ih body body' hb]

/-- The total view preserves the absence of captured-variable annotations. -/
theorem introExp_varsNone (maxApp : Nat) (expression : Exp) :
    fnVarsNoneExp expression ↔ fnVarsNoneExp (introExp maxApp expression) := by
  have run := introExp_bounded 0 maxApp expression
  obtain ⟨fuel, success⟩ := introMultiBounded_origin 0 maxApp expression (introExp maxApp expression) run
  exact introMultiFuel_varsNone fuel maxApp expression (introExp maxApp expression) success

/-- The executable traversal preserves the annotation invariant on programs. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "every_Fn_vs_NONE_intro_multi"]
theorem introList_varsNone (maxApp : Nat) (program : List Exp) :
    everyFnVarsNone (introList maxApp program) ↔ everyFnVarsNone program := by
  apply Iff.symm
  induction program with
  | nil => simp [introList, everyFnVarsNone]
  | cons head tail ih =>
    simp only [introList_cons, everyFnVarsNone, ← introExp_varsNone maxApp head, ← ih]

/-- The total view of one executed traversal preserves application safety. -/
theorem introExp_containsAppSome (maxApp : Nat) (expression : Exp) :
    containsAppSomeExp maxApp expression ↔ containsAppSomeExp maxApp (introExp maxApp expression) := by
  have run := introExp_bounded 0 maxApp expression
  obtain ⟨fuel, success⟩ := introMultiBounded_origin 0 maxApp expression (introExp maxApp expression) run
  exact introMultiFuel_containsAppSome fuel maxApp expression (introExp maxApp expression) success

/-- The executed multi-argument traversal preserves application safety over
complete programs. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "contains_App_SOME_intro_multi"]
theorem introList_containsAppSome (maxApp : Nat) (program : List Exp) :
    containsAppSome maxApp (introList maxApp program) ↔ containsAppSome maxApp program := by
  induction program with
  | nil => simp [introList, containsAppSome]
  | cons head tail ih =>
    simp only [introList_cons, containsAppSome, ← introExp_containsAppSome maxApp head, ih]

end Flapjack.Compiler.Backend.ClosMti
