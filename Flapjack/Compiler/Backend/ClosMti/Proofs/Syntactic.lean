import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMtiSyntactic

/-! Syntactic invariants needed by the pass after multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang ClosProps

/-- Argument collection preserves the absence of captured-variable annotations. -/
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

/-- Application collection preserves the property over the head and arguments. -/
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

/-- The application-safety predicate distributes over appended lists. -/
theorem containsAppSome_append (maxApp : Nat) (left right : List Exp) :
    containsAppSome maxApp (left ++ right) ↔
      containsAppSome maxApp left ∨ containsAppSome maxApp right := by
  induction left with
  | nil => simp [containsAppSome]
  | cons head tail ih => simp [containsAppSome, ih, or_assoc]

/-- Collecting function arguments does not change application safety. This
is a Lean-side collector property pending complete HOL correspondence review. -/
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

/-- The application collector preserves the combined safety condition for its
accumulator and head, including the configured argument limit. -/
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
        simp only [List.length_append, containsAppSome_append] at ih
        simp only [containsAppSomeExp, Option.isSome_none, Bool.false_eq_true, false_or]
        have argsSmall : ¬ maxApp < args.length := by omega
        have moreSmall : ¬ maxApp < more.length := by omega
        have sumSmall : ¬ maxApp < args.length + more.length := by omega
        simp only [argsSmall, moreSmall, sumSmall, false_or] at ih ⊢
        simpa [or_assoc, or_left_comm, or_comm] using ih
      · simp [fits]
  | _ => simp [collectApps]
termination_by sizeOf expression

/-- A pointwise traversal that preserves application safety also preserves it
over the complete list. -/
theorem mapM_containsAppSome (maxApp : Nat) (f : Exp → Option Exp) (source target : List Exp)
    (pointwise : ∀ e result, f e = some result →
      (containsAppSomeExp maxApp e ↔ containsAppSomeExp maxApp result))
    (run : source.mapM f = some target) :
    containsAppSome maxApp source ↔ containsAppSome maxApp target := by
  induction source generalizing target with
  | nil =>
    simp at run
    subst target
    rfl
  | cons first rest ih =>
    cases head : f first with
    | none => simp [List.mapM_cons, head] at run
    | some next =>
      cases tail : rest.mapM f with
      | none => simp [List.mapM_cons, head, tail] at run
      | some nextRest =>
        have equal : next :: nextRest = target := by simpa [List.mapM_cons, head, tail] using run
        subst target
        simp only [containsAppSome, pointwise first next head, ih nextRest tail]

/-- The corresponding traversal property for recursive function bundles. -/
theorem mapM_funs_containsAppSome (maxApp : Nat) (f : Nat × Exp → Option (Nat × Exp))
    (source target : List (Nat × Exp))
    (pointwise : ∀ entry result, f entry = some result →
      (containsAppSomeExp maxApp entry.2 ↔ containsAppSomeExp maxApp result.2))
    (run : source.mapM f = some target) :
    containsAppSomeFuns maxApp source ↔ containsAppSomeFuns maxApp target := by
  induction source generalizing target with
  | nil =>
    simp at run
    subst target
    rfl
  | cons first rest ih =>
    cases head : f first with
    | none => simp [List.mapM_cons, head] at run
    | some next =>
      cases tail : rest.mapM f with
      | none => simp [List.mapM_cons, head, tail] at run
      | some nextRest =>
        have equal : next :: nextRest = target := by simpa [List.mapM_cons, head, tail] using run
        subst target
        cases first
        cases next
        simp only [containsAppSomeFuns, pointwise _ _ head, ih nextRest tail]

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
theorem mapM_varsNone (f : Exp → Option Exp) (source target : List Exp)
    (pointwise : ∀ e result, f e = some result →
      (fnVarsNoneExp e ↔ fnVarsNoneExp result))
    (run : source.mapM f = some target) :
    everyFnVarsNone source ↔ everyFnVarsNone target := by
  induction source generalizing target with
  | nil =>
    simp at run
    subst target
    rfl
  | cons first rest ih =>
    cases head : f first with
    | none => simp [List.mapM_cons, head] at run
    | some next =>
      cases tail : rest.mapM f with
      | none => simp [List.mapM_cons, head, tail] at run
      | some nextRest =>
        have equal : next :: nextRest = target := by simpa [List.mapM_cons, head, tail] using run
        subst target
        simp only [everyFnVarsNone, pointwise first next head, ih nextRest tail]

/-- The corresponding traversal property for recursive function bundles. -/
theorem mapM_funs_varsNone (f : Nat × Exp → Option (Nat × Exp))
    (source target : List (Nat × Exp))
    (pointwise : ∀ entry result, f entry = some result →
      (fnVarsNoneExp entry.2 ↔ fnVarsNoneExp result.2))
    (run : source.mapM f = some target) :
    fnVarsNoneFuns source ↔ fnVarsNoneFuns target := by
  induction source generalizing target with
  | nil =>
    simp at run
    subst target
    rfl
  | cons first rest ih =>
    cases head : f first with
    | none => simp [List.mapM_cons, head] at run
    | some next =>
      cases tail : rest.mapM f with
      | none => simp [List.mapM_cons, head, tail] at run
      | some nextRest =>
        have equal : next :: nextRest = target := by simpa [List.mapM_cons, head, tail] using run
        subst target
        cases first
        cases next
        simp only [fnVarsNoneFuns, pointwise _ _ head, ih nextRest tail]

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
theorem introList_varsNone (maxApp : Nat) (program : List Exp) :
    everyFnVarsNone program ↔ everyFnVarsNone (introList maxApp program) := by
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
complete programs. The original theorem and all carriers still need source
review before this result can be classified as an exact HOL port. -/
theorem introList_containsAppSome (maxApp : Nat) (program : List Exp) :
    containsAppSome maxApp (introList maxApp program) ↔ containsAppSome maxApp program := by
  induction program with
  | nil => simp [introList, containsAppSome]
  | cons head tail ih =>
    simp only [introList_cons, containsAppSome, ← introExp_containsAppSome maxApp head, ih]

/-- A unary program remains eligible for closure numbering after
multi-argument introduction when the application limit is positive. -/
theorem introList_numberingSafe (maxApp : Nat) (program : List Exp)
    (positive : 0 < maxApp) (unary : ∀ e ∈ program, noMti e) :
    ¬ containsAppSome maxApp (introList maxApp program) := by
  intro invalid
  exact (noMtiList_syntactic maxApp positive program unary).2
    ((introList_containsAppSome maxApp program).mp invalid)

/-- The executed optional traversal always returns a numbering-safe program
when its input satisfies the unary invariant and the application limit is positive. -/
theorem compileFuel_numberingSafe (fuel : Nat) (enabled : Bool) (maxApp : Nat) (program : List Exp)
    (positive : 0 < maxApp) (unary : ∀ e ∈ program, noMti e) :
    ∃ result, compileFuel fuel enabled maxApp program = some result ∧
      ¬ containsAppSome maxApp result := by
  cases enabled with
  | false => exact ⟨program, rfl, (noMtiList_syntactic maxApp positive program unary).2⟩
  | true => exact ⟨introList maxApp program, compileFuel_introList fuel maxApp program,
      introList_numberingSafe maxApp program positive unary⟩

end Flapjack.Compiler.Backend.ClosMti
