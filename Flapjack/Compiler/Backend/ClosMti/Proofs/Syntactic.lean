module

public import Flapjack.Misc.Option.MapM
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.Syntactic
public import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
public import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMtiSyntactic
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity
public import Flapjack.Compiler.Backend.ClosMti.Proofs.Traversal

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
      · simp only [fits, if_true]
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
    have funsStep : ∀ source target, source.mapM (collectEntry maxApp fuel) = some target →
        (containsAppSomeFuns maxApp source ↔ containsAppSomeFuns maxApp target) := by
      intro source target run
      apply mapM_funs_containsAppSome maxApp (collectEntry maxApp fuel) source target _ run
      intro entry result run
      cases entry with
      | mk arity body =>
        cases found : collectArgs maxApp arity body with
        | mk count rest =>
          cases step : introMultiFuel fuel maxApp rest with
          | none => simp [collectEntry, found, step] at run
          | some body' =>
            have equal : (count, body') = result := by simpa [collectEntry, found, step] using run
            subst result
            have collector := collectArgs_containsAppSome maxApp arity body
            rw [found] at collector
            exact collector.trans (ih rest body' step)
    exact introMultiFuel_step (fuel := fuel) (maxApp := maxApp)
      (R := fun e r => containsAppSomeExp maxApp e ↔ containsAppSomeExp maxApp r)
      (RList := fun xs ys => containsAppSome maxApp xs ↔ containsAppSome maxApp ys)
      (RFuns := fun fs fs' => containsAppSomeFuns maxApp fs ↔ containsAppSomeFuns maxApp fs')
      (fun _ _ => Iff.rfl)
      (by
        intro t c c' y y' z z' hc hy hz
        simp [containsAppSomeExp, hc, hy, hz])
      (by
        intro t xs xs' b b' hs hb
        simp [containsAppSomeExp, hs, hb])
      (by
        intro t b b' hb
        simpa [containsAppSomeExp] using hb)
      (by
        intro t b b' h h' hb hh
        simp [containsAppSomeExp, hb, hh])
      (by
        intro t b b' hb
        simpa [containsAppSomeExp] using hb)
      (by
        intro t k l xs xs' hs
        simpa [containsAppSomeExp] using hs)
      (by
        intro t l b b' xs xs' hb hs
        simp [containsAppSomeExp])
      (by
        intro t args head argsC headC head' args' collected hlen hhead hargs
        have collector := collectApps_containsAppSome maxApp args head
        rw [collected] at collector
        simp only at collector
        simp only [containsAppSomeExp, Option.isSome_none, Bool.false_eq_true, false_or,
          ← hhead, ← hargs, hlen]
        simpa [or_assoc, or_left_comm, or_comm] using collector)
      (by
        intro t l v a b b' hb
        simpa [containsAppSomeExp] using hb)
      (by
        intro t v a b b' hb
        simpa [containsAppSomeExp] using hb)
      (by
        intro t a b c rest b' collected hrest
        have collector := collectArgs_containsAppSome maxApp a b
        rw [collected] at collector
        simpa [containsAppSomeExp, hrest] using collector)
      (by
        intro t fs fs' b b' hfs hb
        simp [containsAppSomeExp, hfs, hb])
      (by
        intro t l v fs b b' hb
        simp [containsAppSomeExp, hb])
      (by
        intro t v fs b b' hb
        simp [containsAppSomeExp, hb])
      (by
        intro t o xs xs' hs
        cases o with
        | thunkOp operation =>
          cases operation with
          | forceThunk => simp [containsAppSomeExp, hs]
          | allocThunk _ => simp [containsAppSomeExp, hs]
          | updateThunk _ => simp [containsAppSomeExp, hs]
        | _ => simp [containsAppSomeExp, hs])
      listStep funsStep ih run



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
    have funsStep : ∀ source target, source.mapM (collectEntry maxApp fuel) = some target →
        (fnVarsNoneFuns source ↔ fnVarsNoneFuns target) := by
      intro source target run
      apply mapM_funs_varsNone (collectEntry maxApp fuel) source target _ run
      intro entry result run
      cases entry with
      | mk arity body =>
        cases found : collectArgs maxApp arity body with
        | mk count rest =>
          cases step : introMultiFuel fuel maxApp rest with
          | none => simp [collectEntry, found, step] at run
          | some body' =>
            have equal : (count, body') = result := by simpa [collectEntry, found, step] using run
            subst result
            have collector := collectArgs_varsNone maxApp arity body
            rw [found] at collector
            exact collector.trans (ih rest body' step)
    exact introMultiFuel_step (fuel := fuel) (maxApp := maxApp)
      (R := fun e r => fnVarsNoneExp e ↔ fnVarsNoneExp r)
      (RList := fun xs ys => everyFnVarsNone xs ↔ everyFnVarsNone ys)
      (RFuns := fun fs fs' => fnVarsNoneFuns fs ↔ fnVarsNoneFuns fs')
      (fun _ _ => Iff.rfl)
      (by
        intro t c c' y y' z z' hc hy hz
        simp [fnVarsNoneExp, hc, hy, hz])
      (by
        intro t xs xs' b b' hs hb
        simp [fnVarsNoneExp, hs, hb])
      (by
        intro t b b' hb
        simpa [fnVarsNoneExp] using hb)
      (by
        intro t b b' h h' hb hh
        simp [fnVarsNoneExp, hb, hh])
      (by
        intro t b b' hb
        simpa [fnVarsNoneExp] using hb)
      (by
        intro t k l xs xs' hs
        simpa [fnVarsNoneExp] using hs)
      (by
        intro t l b b' xs xs' hb hs
        simp [fnVarsNoneExp, hb, hs])
      (by
        intro t args head argsC headC head' args' collected hlen hhead hargs
        have collector := collectApps_varsNone maxApp args head
        rw [collected] at collector
        simp only at collector
        simp only [fnVarsNoneExp, ← hhead, ← hargs]
        simpa [and_comm] using collector)
      (by
        intro t l v a b b' hb
        simp [fnVarsNoneExp, hb])
      (by
        intro t v a b b' hb
        simp [fnVarsNoneExp])
      (by
        intro t a b c rest b' collected hrest
        have collector := collectArgs_varsNone maxApp a b
        rw [collected] at collector
        simpa [fnVarsNoneExp] using collector.trans hrest)
      (by
        intro t fs fs' b b' hfs hb
        simp [fnVarsNoneExp, hfs, hb])
      (by
        intro t l v fs b b' hb
        simp [fnVarsNoneExp, hb])
      (by
        intro t v fs b b' hb
        simp [fnVarsNoneExp])
      (by
        intro t o xs xs' hs
        simpa [fnVarsNoneExp] using hs)
      listStep funsStep ih run



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

/-- Optional multi-argument compilation preserves application safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "contains_App_SOME_compile"]
theorem compile_containsAppSome (enabled : Bool) (maxApp : Nat) (program : List Exp) :
    containsAppSome maxApp (compile enabled maxApp program) ↔ containsAppSome maxApp program := by
  cases enabled <;> simp [compile, introList_containsAppSome]

/-- Multi-argument compilation returns an empty list exactly for an empty input. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "compile_EQ_NIL"]
theorem compile_eq_nil (enabled : Bool) (maxApp : Nat) (program : List Exp) :
    compile enabled maxApp program = [] ↔ program = [] := by
  cases enabled <;> simp [compile, introList]

/-- Multi-argument introduction returns an empty list exactly for an empty input. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "intro_multi_EQ_NIL"]
theorem introList_eq_nil (maxApp : Nat) (program : List Exp) :
    introList maxApp program = [] ↔ program = [] := by
  simp [introList]

/-- Multi-argument introduction preserves the empty list. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "intro_multi_nil"]
theorem introList_nil (maxApp : Nat) : introList maxApp [] = [] := by
  exact (introList_eq_nil maxApp []).2 rfl

/-- The eta-normalized source equations for the pre-multi-argument invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "no_mti_def"]
theorem noMti_eqns :
    (∀ (t : BackendCommon.Tra) (n : Nat), noMti (.var t n) ↔ True) ∧
    (∀ (t : BackendCommon.Tra) (e3 e2 e1 : Exp), noMti (.ifThenElse t e1 e2 e3) ↔
      noMti e1 ∧ noMti e2 ∧ noMti e3) ∧
    (∀ (t : BackendCommon.Tra) (es : List Exp) (e : Exp), noMti (.let t es e) ↔
      (∀ x ∈ es, noMti x) ∧ noMti e) ∧
    (∀ (t : BackendCommon.Tra) (e : Exp), noMti (.raise t e) ↔ noMti e) ∧
    (∀ (t : BackendCommon.Tra) (e2 e1 : Exp), noMti (.handle t e1 e2) ↔ noMti e1 ∧ noMti e2) ∧
    (∀ (t : BackendCommon.Tra) (e : Exp), noMti (.tick t e) ↔ noMti e) ∧
    (∀ (ticks : Nat) (t : BackendCommon.Tra) (n : Nat) (es : List Exp), noMti (.call t ticks n es) ↔ False) ∧
    (∀ (t : BackendCommon.Tra) (opt : Option Nat) (es : List Exp) (e : Exp), noMti (.app t opt e es) ↔
      es.length = 1 ∧ opt = none ∧ (∀ x ∈ es, noMti x) ∧ noMti e) ∧
    (∀ (t : Flapjack.Basis.Pure.MlString.MlString) (opt2 : Option (List Nat)) (opt1 : Option Nat)
      (arity : Nat) (e : Exp), noMti (.fn t opt1 opt2 arity e) ↔
      arity = 1 ∧ opt1 = none ∧ opt2 = none ∧ noMti e) ∧
    (∀ (t : List Flapjack.Basis.Pure.MlString.MlString) (opt2 : Option (List Nat)) (opt1 : Option Nat)
      (funs : List (Nat × Exp)) (e : Exp), noMti (.letrec t opt1 opt2 funs e) ↔
      noMti e ∧ opt1 = none ∧ opt2 = none ∧ (∀ x ∈ funs, x.1 = 1 ∧ noMti x.2)) ∧
    (∀ (t : BackendCommon.Tra) (op : Op) (es : List Exp), noMti (.op t op es) ↔ ∀ x ∈ es, noMti x) := by
  simp [noMti, noMtiList_iff, noMtiFuns_iff]

end Flapjack.Compiler.Backend.ClosMti
