module

public import Flapjack.Compiler.Backend.Semantics.DataProps.AppWithLocals
public import Flapjack.Compiler.Backend.Semantics.DataProps.PrimitiveResources
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceMonotonicity
public import Flapjack.HolRef

@[expose] public section

/-!
# Stack maximum against the configured stack limit

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:3304`
`do_app_stack_max_le_stack_limit` and `:3330`
`evaluate_stack_max_le_stack_limit`. Once a run stays space-safe, its recorded
stack maximum stays within the configured stack limit: the stack stage records
the maximum of the previous maximum and the new stack size, and its safety flag
witnesses that the new size is below the limit.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.DataSem

section

set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
set_option aesop.warn.nonterminal false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Successful non-FFI applications preserve the configured limits.
    Flapjack infrastructure for `do_app_stack_max_le_stack_limit`; no separate
    HOL original. -/
theorem applyNonFfi_limits {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state next : State C F) (value : Value)
    (run : applyNonFfi op values state = some (value, next)) :
    next.limits = state.limits := by
  simp only [applyNonFfi, Option.bind] at run ⊢
  all_goals repeat' (first | split at run | split) <;>
    simp_all [withFreshTimestamp, checkLim, Option.bind]
  all_goals try (aesop (config := {warnOnNonterminal := false}))
  all_goals try (simp_all [withFreshTimestamp, checkLim])
  all_goals try (aesop (add simp [Option.bind_eq_some_iff]))

/-- Successful auxiliary applications do not change the configured limits.
    Flapjack infrastructure for `do_app_stack_max_le_stack_limit`; no separate
    HOL original. -/
theorem doAppAux_limits {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux op values state = .val (value, next)) :
    next.limits = state.limits := by
  cases op with
  | ffi name =>
    rcases values with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;>
      simp only [doAppAux] at run
    all_goals repeat' (first | split at run | simp_all)
    all_goals rcases run with ⟨_, rfl⟩
    all_goals simp
  | intOp o =>
    cases h : applyNonFfi (.intOp o) values state with
    | none =>
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
      exact applyNonFfi_limits (.intOp o) values state next value h
  | wordOp o =>
    cases h : applyNonFfi (.wordOp o) values state with
    | none =>
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
      exact applyNonFfi_limits (.wordOp o) values state next value h
  | label l =>
    cases h : applyNonFfi (.label l) values state with
    | none =>
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
      exact applyNonFfi_limits (.label l) values state next value h
  | install =>
    cases h : applyNonFfi (.install) values state with
    | none =>
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
      exact applyNonFfi_limits (.install) values state next value h
  | thunkOp o =>
    cases h : applyNonFfi (.thunkOp o) values state with
    | none =>
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
      exact applyNonFfi_limits (.thunkOp o) values state next value h
  | globOp o =>
    cases h : applyNonFfi (.globOp o) values state with
    | none =>
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
      exact applyNonFfi_limits (.globOp o) values state next value h
  | blockOp o =>
    cases h : applyNonFfi (.blockOp o) values state with
    | none =>
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
      exact applyNonFfi_limits (.blockOp o) values state next value h
  | memOp o =>
    cases h : applyNonFfi (.memOp o) values state with
    | none =>
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      simp only [doAppAux] at run
      simp only [h] at run
      cases run
      exact applyNonFfi_limits (.memOp o) values state next value h

end

/-- The stack stage keeps the recorded maximum within the limit whenever its
    safety flag is set.  Flapjack infrastructure for
    `do_app_stack_max_le_stack_limit`; no separate HOL original. -/
theorem doStack_stackMax_le {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F)
    (bound : BackendProps.optionLe state.stackMax (some state.limits.stackLimit))
    (safe : (doStack op values state).safeForSpace = true) :
    BackendProps.optionLe (doStack op values state).stackMax
      (some state.limits.stackLimit) := by
  have flag : ((Option.map₂ (· + ·) (stackConsumed state.stackFrameSizes state.limits op values)
      (Option.map₂ (· + ·) (sizeOfStack state.stack) state.localsSize)).map
        (fun n => decide (state.limits.stackLimit > n))).getD false = true := by
    have hs := safe
    simp only [doStack, Bool.and_eq_true] at hs
    exact hs.2
  have newBound : BackendProps.optionLe
      (Option.map₂ (· + ·) (stackConsumed state.stackFrameSizes state.limits op values)
        (Option.map₂ (· + ·) (sizeOfStack state.stack) state.localsSize))
      (some state.limits.stackLimit) := by
    rcases hnew : Option.map₂ (· + ·) (stackConsumed state.stackFrameSizes state.limits op values)
        (Option.map₂ (· + ·) (sizeOfStack state.stack) state.localsSize) with _ | fresh
    · rw [hnew] at flag
      simp only [Option.map_none, Option.getD_none] at flag
      simp at flag
    · have hflag := flag
      rw [hnew] at hflag
      simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at hflag
      simp only [BackendProps.optionLe]
      omega
  simp only [doStack]
  exact (BackendProps.optionLe_max state.stackMax _ (some state.limits.stackLimit)).2
    ⟨bound, newBound⟩

/-- The dispatcher's space branch is the auxiliary application over the limit
    and stack stages for every non-installation operation.  Flapjack
    infrastructure for `do_app_stack_max_le_stack_limit`; no separate HOL
    original. -/
theorem doApp_of_space {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) (hInstall : op ≠ .install) (hGreater : op ≠ .intOp .greater)
    (hGreaterEq : op ≠ .intOp .greaterEq) :
    doApp op values state =
      (match doSpace op values state with
        | none => .err (.abort .typeError)
        | some next => doAppAux op values (doStack op values (doLimSafe next op values))) := by
  cases op <;> simp_all [doApp] <;> try rfl

/-- The shared body of the primitive case: a safe auxiliary result over the
    limit and stack stages keeps the stack maximum within the limit.  Flapjack
    infrastructure for `do_app_stack_max_le_stack_limit`; no separate HOL
    original. -/
theorem doApp_stackMax_le_of_aux {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state accounted : State C F) (res : Value) (next : State C F)
    (space : doSpace op values state = some accounted)
    (aux : doAppAux op values (doStack op values (doLimSafe accounted op values)) =
      .val (res, next))
    (safe : next.safeForSpace = true)
    (bound : BackendProps.optionLe state.stackMax (some state.limits.stackLimit)) :
    BackendProps.optionLe next.stackMax (some next.limits.stackLimit) := by
  obtain ⟨_, _, _, spaceLimits, spaceMax, _⟩ := doSpace_fields op values state accounted space
  have stackSafe : (doStack op values (doLimSafe accounted op values)).safeForSpace = true :=
    (doAppAux_resource_frame op values (doStack op values (doLimSafe accounted op values))
      next res aux).2.2 safe
  have limEq : (doLimSafe accounted op values).limits.stackLimit = state.limits.stackLimit := by
    simp [doLimSafe, spaceLimits]
  have maxEq : (doLimSafe accounted op values).stackMax = state.stackMax := by
    simp [doLimSafe, spaceMax]
  have boundLim : BackendProps.optionLe (doLimSafe accounted op values).stackMax
      (some (doLimSafe accounted op values).limits.stackLimit) := by
    rw [maxEq, limEq]
    exact bound
  have stackBound := doStack_stackMax_le op values (doLimSafe accounted op values)
    boundLim stackSafe
  have nextStack := (doAppAux_fieldFrame op values
    (doStack op values (doLimSafe accounted op values)) next res aux).2.2.1
  have nextLimits := doAppAux_limits op values
    (doStack op values (doLimSafe accounted op values)) next res aux
  have stackLimits : (doStack op values (doLimSafe accounted op values)).limits.stackLimit =
      state.limits.stackLimit := by
    simp [doStack, limEq]
  rw [nextStack, nextLimits, stackLimits]
  simpa [limEq] using stackBound

/-- Exact HOL `do_app_stack_max_le_stack_limit`
    (`dataPropsScript.sml:3304`): a successful application that stays
    space-safe keeps the recorded stack maximum within the stack limit. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_stack_max_le_stack_limit"]
theorem doApp_stackMax_le_stackLimit {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) (res : Value) (next : State C F)
    (premises : doApp op values state = .val (res, next) ∧ next.safeForSpace = true ∧
      BackendProps.optionLe state.stackMax (some state.limits.stackLimit)) :
    BackendProps.optionLe next.stackMax (some next.limits.stackLimit) := by
  obtain ⟨run, safe, bound⟩ := premises
  by_cases install : op = .install
  · subst install
    simp only [doApp] at run
    obtain ⟨_, _, cleared⟩ := doInstall_resource_frame values _ next res run
    rw [cleared] at safe
    simp at safe
  · by_cases greater : op = .intOp .greater
    · subst greater
      simp only [doApp] at run
      simp at run
    · by_cases greaterEq : op = .intOp .greaterEq
      · subst greaterEq
        simp only [doApp] at run
        simp at run
      · rw [doApp_of_space op values state install greater greaterEq] at run
        cases hspace : doSpace op values state with
        | none =>
          simp only [hspace] at run
          simp at run
        | some accounted =>
          simp only [hspace] at run
          exact doApp_stackMax_le_of_aux op values state accounted res next hspace run safe bound

end Flapjack.Compiler.Backend.DataProps
