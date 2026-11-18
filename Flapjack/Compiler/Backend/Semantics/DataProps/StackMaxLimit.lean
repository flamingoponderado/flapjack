module

public import Flapjack.Compiler.Backend.Semantics.DataProps.AppWithLocals
public import Flapjack.Compiler.Backend.Semantics.DataProps.PrimitiveResources
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceMonotonicity
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall
public import Flapjack.Compiler.Backend.Semantics.DataProps.CutSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.CutFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.Jump
public import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock
public import Flapjack.Misc.ClockWeightInduction
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

/-- Along a safe run, the recorded stack maximum stays within the configured
    stack limit. -/
private def StackMaxLimitAt {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  ∀ (res : Option (Flapjack.SemanticPrimitivesHOL.Result (List DataSem.Value) DataSem.Value))
    (next : State C F),
    evaluate program state = (res, next) → next.safeForSpace = true →
    BackendProps.optionLe state.stackMax (some state.limits.stackLimit) →
    BackendProps.optionLe next.stackMax (some next.limits.stackLimit)

/-- The narrow local cut leaves the configured limits untouched.  Flapjack
    infrastructure for `evaluate_stack_max_le_stack_limit`; no separate HOL
    original. -/
private theorem cutStateOpt_limits {C F : Type} (names : Option NumSet)
    (state next : State C F) (run : cutStateOpt names state = some next) :
    next.limits = state.limits := by
  cases names with
  | none =>
    simp only [cutStateOpt, Option.some.injEq] at run
    rw [← run]
  | some names =>
    simp only [cutStateOpt, cutState] at run
    cases found : cutEnv names state.locals with
    | none => simp [found] at run
    | some env =>
      simp only [found, Option.map_some, Option.some.injEq] at run
      rw [← run]

private theorem stackMaxLimitAt_skip {C F : Type} (state : State C F) :
    StackMaxLimitAt .skip state := by
  intro res next run safe bound
  simp only [evaluate, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  exact bound

private theorem stackMaxLimitAt_move {C F : Type} (dest src : Nat) (state : State C F) :
    StackMaxLimitAt (.move dest src) state := by
  intro res next run safe bound
  cases read : DataSem.getVar src state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact bound
  | some value =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    simpa [setVar] using bound

private theorem stackMaxLimitAt_assign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : Option NumSet) (state : State C F) :
    StackMaxLimitAt (.assign dest op names live) state := by
  intro res next run safe bound
  simp only [evaluate] at run ⊢
  by_cases requires : (DataLang.opRequiresNames op == live.isNone) = true
  · rw [if_pos requires] at run
    simp [typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    exact bound
  · rw [if_neg requires] at run
    cases read : DataSem.getVars names state.locals with
    | none =>
      simp [read, typeError] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      exact bound
    | some values =>
      simp only [read] at run ⊢
      cases cut : cutStateOpt live state with
      | none =>
        simp [cut, typeError] at run ⊢
        obtain ⟨rfl, rfl⟩ := run
        exact bound
      | some mid =>
        simp only [cut] at run ⊢
        have midMax := cutStateOpt_stackMax live state mid cut
        have midLim := cutStateOpt_limits live state mid cut
        have midBound : BackendProps.optionLe mid.stackMax (some mid.limits.stackLimit) := by
          rw [midMax, midLim]
          exact bound
        cases app : doApp op values mid with
        | err error =>
          simp only [app] at run
          obtain ⟨rfl, rfl⟩ := run
          simpa [flushState, installSfs, midLim] using midBound
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp only [app] at run
          obtain ⟨rfl, rfl⟩ := run
          have lastSafe : last.safeForSpace = true := by
            by_cases install : op = .install
            · subst install
              simp [setVar, installSfs] at safe
            · simp only [setVar, installSfs] at safe
              exact safe
          have lastBound := doApp_stackMax_le_stackLimit op values mid value last
            ⟨app, lastSafe, midBound⟩
          simpa [setVar, installSfs] using lastBound

private theorem stackMaxLimitAt_tick {C F : Type} (state : State C F) :
    StackMaxLimitAt .tick state := by
  intro res next run safe bound
  simp only [evaluate] at run ⊢
  by_cases zero : state.clock = 0
  · rw [if_pos zero] at run
    simp [timeoutError, flushState] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    simpa [flushState] using bound
  · rw [if_neg zero] at run
    simp [decClock] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    simpa [decClock] using bound

private theorem stackMaxLimitAt_makeSpace {C F : Type} (amount : Nat) (names : NumSet)
    (state : State C F) : StackMaxLimitAt (.makeSpace amount names) state := by
  intro res next run safe bound
  simp only [evaluate] at run ⊢
  cases cut : cutEnv names state.locals with
  | none =>
    simp [cut, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    exact bound
  | some env =>
    simp only [cut] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    simpa [addSpace] using bound

private theorem stackMaxLimitAt_raise {C F : Type} (name : Nat) (state : State C F) :
    StackMaxLimitAt (.raise name) state := by
  intro res next run safe bound
  simp only [evaluate] at run ⊢
  cases read : DataSem.getVar name state.locals with
  | none =>
    simp [read, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    exact bound
  | some value =>
    simp only [read] at run ⊢
    generalize jumpEq : jumpExc state = jump at run ⊢
    by_cases hasJump : ∃ t : State C F, jumpExc state = some t
    · obtain ⟨target, targetRun⟩ := hasJump
      have jumpSome : jump = some target := by
        rw [← jumpEq, targetRun]
      rw [jumpSome] at run
      simp only [] at run ⊢
      have nextEq : next = target := by simpa using (congrArg Prod.snd run).symm
      rw [nextEq]
      obtain ⟨_, n, e, ls, xs, _, targetEq⟩ := jumpExcImp state target targetRun
      rw [targetEq]
      simpa using bound
    · have jumpNone : jump = none := by
        rw [← jumpEq]
        cases found : jumpExc state with
        | none => rfl
        | some t => exact absurd ⟨t, found⟩ hasJump
      rw [jumpNone] at run
      simp only [] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      exact bound

private theorem stackMaxLimitAt_return {C F : Type} (names : List Nat) (state : State C F) :
    StackMaxLimitAt (.return names) state := by
  intro res next run safe bound
  simp only [evaluate] at run ⊢
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp [read, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    exact bound
  | some values =>
    simp only [read] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    simpa [flushState] using bound

private theorem stackMaxLimitAt_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (state : State C F) (yesIH : StackMaxLimitAt yes state) (noIH : StackMaxLimitAt no state) :
    StackMaxLimitAt (.ifThenElse name yes no) state := by
  intro res next run safe bound
  simp only [evaluate] at run ⊢
  cases read : DataSem.getVar name state.locals with
  | none =>
    simp [read, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    exact bound
  | some value =>
    simp only [read] at run ⊢
    by_cases isTrue : DataSem.isBool true value = true
    · rw [if_pos isTrue] at run
      exact yesIH res next run safe bound
    · by_cases isFalse : DataSem.isBool false value = true
      · rw [if_neg isTrue, if_pos isFalse] at run
        exact noIH res next run safe bound
      · rw [if_neg isTrue, if_neg isFalse] at run
        simp [typeError] at run ⊢
        obtain ⟨rfl, rfl⟩ := run
        exact bound

private theorem stackMaxLimitAt_seq {C F : Type} (first second : DataLang.Prog)
    (state : State C F) (firstIH : StackMaxLimitAt first state)
    (secondIH : ∀ mid : State C F, mid.clock ≤ state.clock → StackMaxLimitAt second mid) :
    StackMaxLimitAt (.seq first second) state := by
  intro res next run safe bound
  simp only [evaluate] at run ⊢
  cases firstRun : evaluate first state with
  | mk outcome mid =>
    rw [firstRun] at run
    simp only [fixClock] at run ⊢
    cases outcome with
    | none =>
      simp only [] at run
      have clockLe : (fixClock state ((none : Option (SemanticPrimitivesHOL.Result
          (List DataSem.Value) DataSem.Value)), mid)).2.clock ≤ state.clock := by
        simp only [fixClock]
        exact Nat.min_le_left _ _
      have midSafe : (fixClock state ((none : Option (SemanticPrimitivesHOL.Result
          (List DataSem.Value) DataSem.Value)), mid)).2.safeForSpace = true :=
        evaluate_safety_of_result second
          (fixClock state ((none : Option (SemanticPrimitivesHOL.Result
            (List DataSem.Value) DataSem.Value)), mid)).2 res next ⟨run, safe⟩
      have midBound : BackendProps.optionLe (fixClock state ((none : Option
            (SemanticPrimitivesHOL.Result (List DataSem.Value) DataSem.Value)), mid)).2.stackMax
          (some (fixClock state ((none : Option (SemanticPrimitivesHOL.Result
            (List DataSem.Value) DataSem.Value)), mid)).2.limits.stackLimit) := by
        simpa only [fixClock] using firstIH none mid firstRun midSafe bound
      exact secondIH (fixClock state ((none : Option (SemanticPrimitivesHOL.Result
        (List DataSem.Value) DataSem.Value)), mid)).2 clockLe res next run safe midBound
    | some result =>
      simp only [] at run
      obtain ⟨rfl, rfl⟩ := run
      simpa only [fixClock] using firstIH (some result) mid firstRun safe bound

end Flapjack.Compiler.Backend.DataProps
