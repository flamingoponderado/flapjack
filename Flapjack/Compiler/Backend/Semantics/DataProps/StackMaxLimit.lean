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

set_option linter.unusedSimpArgs false
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

/-- A `decide`-mapped bound gives the optional bound.  Flapjack infrastructure
    for `evaluate_stack_max_le_stack_limit`; no separate HOL original. -/
private theorem optionLe_of_decideMap (n : Nat) (m : Option Nat)
    (h : (Option.map (fun x => decide (n > x)) m).getD false = true) :
    BackendProps.optionLe m (some n) := by
  cases m with
  | none => simp at h
  | some x =>
    simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at h
    simp only [BackendProps.optionLe]
    omega

/-- Entering a call with a set safety flag keeps the stack maximum within the
    limit.  Flapjack infrastructure for `evaluate_stack_max_le_stack_limit`; no
    separate HOL original. -/
private theorem callEnv_stackMax_le {C F : Type} (args : List Value) (size : Option Nat)
    (state : State C F) (safe : (DataSem.callEnv args size state).safeForSpace = true) :
    BackendProps.optionLe (DataSem.callEnv args size state).stackMax
      (some state.limits.stackLimit) := by
  have hs := safe
  simp only [DataSem.callEnv, Bool.and_eq_true] at hs ⊢
  exact optionLe_of_decideMap state.limits.stackLimit _ hs.2

/-- Pushing a call frame with a set safety flag keeps the stack maximum within
    the limit.  Flapjack infrastructure for `evaluate_stack_max_le_stack_limit`;
    no separate HOL original. -/
private theorem pushEnv_stackMax_le {C F : Type} (env : Spt Value) (handler : Bool)
    (state : State C F) (safe : (DataSem.pushEnv env handler state).safeForSpace = true) :
    BackendProps.optionLe (DataSem.pushEnv env handler state).stackMax
      (some state.limits.stackLimit) := by
  have hs := safe
  simp only [DataSem.pushEnv, Bool.and_eq_true] at hs ⊢
  exact optionLe_of_decideMap state.limits.stackLimit _ hs.2

/-- Clamp a state's clock, retaining every other field.  Flapjack
    infrastructure for `evaluate_stack_max_le_stack_limit`; no separate HOL
    original. -/
private def clampClock {C F : Type} (state : State C F) (clock : Nat) : State C F :=
  { state with clock := clock }

/-- Frame restoration keeps the stack maximum and the configured limits, even
    after the clock clamp.  Flapjack infrastructure for
    `evaluate_stack_max_le_stack_limit`; no separate HOL original. -/
private theorem popEnv_stackMax {C F : Type} (state : State C F) (clock : Nat)
    (popped : State C F) (run : DataSem.popEnv (clampClock state clock) = some popped) :
    popped.stackMax = state.stackMax ∧ popped.limits = state.limits ∧
      popped.safeForSpace = state.safeForSpace := by
  cases stack : state.stack with
  | nil => simp [DataSem.popEnv, clampClock, stack] at run
  | cons frame rest =>
    cases frame with
    | env size envSpt =>
      simp only [DataSem.popEnv, clampClock, stack, Option.some.injEq] at run
      cases run
      exact ⟨rfl, rfl, rfl⟩
    | exc size envSpt frameHandler =>
      simp only [DataSem.popEnv, clampClock, stack, Option.some.injEq] at run
      cases run
      exact ⟨rfl, rfl, rfl⟩

/-- The returning-force dispatch keeps the stack maximum within the limit.
    Flapjack infrastructure for `evaluate_stack_max_le_stack_limit`; no separate
    HOL original. -/
private theorem stackMaxLimitAt_force {C F : Type} (ret : Option (Nat × NumSet))
    (label src : Nat) (state : State C F)
    (bodyIH : ∀ body : DataLang.Prog, ∀ next : State C F, next.clock < state.clock →
      StackMaxLimitAt body next) :
    StackMaxLimitAt (.force ret label src) state := by
  intro res next run safe bound
  simp only [evaluate] at run ⊢
  cases read : DataSem.getVar src state.locals with
  | none =>
    simp [read, typeError] at run ⊢
    obtain ⟨_, rfl⟩ := run
    exact bound
  | some thunk =>
    simp only [read] at run ⊢
    generalize destEq : DataSem.destThunk thunk state.refs = dest at run ⊢
    cases dest with
    | badRef =>
      simp only [] at run ⊢
      simp [typeError] at run ⊢
      obtain ⟨_, rfl⟩ := run
      exact bound
    | notThunk =>
      simp only [] at run ⊢
      simp [typeError] at run ⊢
      obtain ⟨_, rfl⟩ := run
      exact bound
    | isThunk flag payload =>
      cases flag with
      | evaluated =>
        simp only [] at run ⊢
        cases ret with
        | none =>
          simp only [] at run ⊢
          simp [flushState] at run ⊢
          obtain ⟨_, rfl⟩ := run
          simpa [flushState] using bound
        | some retPair =>
          obtain ⟨target, names⟩ := retPair
          simp only [] at run ⊢
          cases cut : DataSem.cutEnv names state.locals with
          | none =>
            simp [cut, typeError] at run ⊢
            obtain ⟨_, rfl⟩ := run
            exact bound
          | some env =>
            simp only [cut] at run ⊢
            simp at run ⊢
            obtain ⟨_, rfl⟩ := run
            simpa [setVar] using bound
      | notEvaluated =>
        simp only [] at run ⊢
        generalize foundEq : DataSem.findCode (some label) [thunk, payload] state.code
          state.stackFrameSizes = found at run ⊢
        cases found with
        | none =>
          simp [typeError] at run ⊢
          obtain ⟨_, rfl⟩ := run
          exact bound
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          simp only [] at run ⊢
          cases ret with
          | none =>
            simp only [] at run ⊢
            by_cases zero : state.clock = 0
            · rw [if_pos zero] at run
              simp [timeoutError] at run ⊢
              obtain ⟨_, rfl⟩ := run
              simpa using bound
            · rw [if_neg zero] at run
              cases bodyRun : evaluate body (DataSem.callEnv args size (decClock state)) with
              | mk bodyRes last =>
                rw [bodyRun] at run
                simp only [] at run
                have bodyBound : ∀ (bodyRes : Option (SemanticPrimitivesHOL.Result
                    (List Value) Value)) (last : State C F),
                    evaluate body (DataSem.callEnv args size (decClock state)) =
                      (bodyRes, last) →
                    last.safeForSpace = true →
                    BackendProps.optionLe last.stackMax (some last.limits.stackLimit) := by
                  intro bodyRes last bodyRun lastSafe
                  have callSafe := evaluate_safety_of_result body
                    (DataSem.callEnv args size (decClock state)) bodyRes last ⟨bodyRun, lastSafe⟩
                  have boundCall : BackendProps.optionLe
                      (DataSem.callEnv args size (decClock state)).stackMax
                      (some (DataSem.callEnv args size (decClock state)).limits.stackLimit) := by
                    simpa only [DataSem.callEnv] using
                      callEnv_stackMax_le args size (decClock state) callSafe
                  have clockLt :
                      (DataSem.callEnv args size (decClock state)).clock < state.clock := by
                    simp only [DataSem.callEnv, decClock]
                    omega
                  exact bodyIH body (DataSem.callEnv args size (decClock state)) clockLt
                    bodyRes last bodyRun lastSafe boundCall
                cases bodyRes with
                | none =>
                  simp only [typeError, Prod.mk.injEq] at run
                  obtain ⟨_, rfl⟩ := run
                  have lastSafe : last.safeForSpace = true := by simpa using safe
                  simpa using bodyBound none last bodyRun lastSafe
                | some value =>
                  simp only [Prod.mk.injEq] at run
                  obtain ⟨_, rfl⟩ := run
                  have lastSafe : last.safeForSpace = true := by simpa using safe
                  simpa using bodyBound (some value) last bodyRun lastSafe
          | some retPair =>
            obtain ⟨target, names⟩ := retPair
            simp only [] at run ⊢
            cases cut : DataSem.cutEnv names state.locals with
            | none =>
              simp [cut, typeError] at run ⊢
              obtain ⟨_, rfl⟩ := run
              exact bound
            | some env =>
              simp only [cut] at run ⊢
              by_cases zero : state.clock = 0
              · rw [if_pos zero] at run
                simp [timeoutError] at run ⊢
                obtain ⟨_, rfl⟩ := run
                have callSafe : (DataSem.callEnv args size
                    (DataSem.pushEnv env false (decClock state))).safeForSpace = true := by
                  simpa using safe
                simpa only [DataSem.callEnv, DataSem.pushEnv, decClock] using
                  callEnv_stackMax_le args size
                    (DataSem.pushEnv env false (decClock state)) callSafe
              · rw [if_neg zero] at run
                simp only [fixClock] at run ⊢
                cases bodyRun : evaluate body
                    (DataSem.callEnv args size (DataSem.pushEnv env false (decClock state))) with
                | mk bodyRes last =>
                  rw [bodyRun] at run
                  simp only [] at run
                  have bodyBound : ∀ (bodyRes : Option (SemanticPrimitivesHOL.Result
                      (List Value) Value)) (last : State C F),
                      evaluate body (DataSem.callEnv args size
                        (DataSem.pushEnv env false (decClock state))) = (bodyRes, last) →
                      last.safeForSpace = true →
                      BackendProps.optionLe last.stackMax (some last.limits.stackLimit) := by
                    intro bodyRes last bodyRun lastSafe
                    have callSafe := evaluate_safety_of_result body
                      (DataSem.callEnv args size (DataSem.pushEnv env false (decClock state)))
                      bodyRes last ⟨bodyRun, lastSafe⟩
                    have boundCall : BackendProps.optionLe
                        (DataSem.callEnv args size
                          (DataSem.pushEnv env false (decClock state))).stackMax
                        (some (DataSem.callEnv args size
                          (DataSem.pushEnv env false (decClock state))).limits.stackLimit) := by
                      simpa only [DataSem.callEnv] using
                        callEnv_stackMax_le args size
                          (DataSem.pushEnv env false (decClock state)) callSafe
                    have clockLt :
                        (DataSem.callEnv args size
                          (DataSem.pushEnv env false (decClock state))).clock < state.clock := by
                      simp only [DataSem.callEnv, DataSem.pushEnv, decClock]
                      omega
                    exact bodyIH body
                      (DataSem.callEnv args size (DataSem.pushEnv env false (decClock state)))
                      clockLt bodyRes last bodyRun lastSafe boundCall
                  cases bodyRes with
                  | none =>
                    simp only [typeError, Prod.mk.injEq] at run
                    obtain ⟨_, rfl⟩ := run
                    have lastSafe : last.safeForSpace = true := by simpa using safe
                    simpa using bodyBound none last bodyRun lastSafe
                  | some result =>
                    cases result with
                    | val values =>
                      cases values with
                      | nil =>
                        simp only [typeError, Prod.mk.injEq] at run
                        obtain ⟨_, rfl⟩ := run
                        have lastSafe : last.safeForSpace = true := by simpa using safe
                        simpa using bodyBound (some (.val [])) last bodyRun lastSafe
                      | cons value rest =>
                        cases rest with
                        | nil =>
                          cases pop : DataSem.popEnv
                              { last with clock :=
                                  (min (DataSem.callEnv args size
                                    (DataSem.pushEnv env false (decClock state))).clock
                                    last.clock) } with
                          | none =>
                            simp only [pop, typeError, Prod.mk.injEq] at run
                            obtain ⟨_, rfl⟩ := run
                            have lastSafe : last.safeForSpace = true := by simpa using safe
                            simpa using bodyBound (some (.val [value])) last bodyRun lastSafe
                          | some popped =>
                            simp only [pop, Prod.mk.injEq] at run
                            obtain ⟨_, rfl⟩ := run
                            have poppedFacts := popEnv_stackMax last
                              (min (DataSem.callEnv args size
                                (DataSem.pushEnv env false (decClock state))).clock
                                last.clock) popped pop
                            have lastSafe : last.safeForSpace = true := by
                              have hs := safe
                              simp only [setVar] at hs
                              rw [poppedFacts.2.2] at hs
                              exact hs
                            have poppedBound : BackendProps.optionLe popped.stackMax
                                (some popped.limits.stackLimit) := by
                              rw [poppedFacts.1, poppedFacts.2.1]
                              simpa using bodyBound (some (.val [value])) last bodyRun lastSafe
                            simpa [setVar] using poppedBound
                        | cons more rest' =>
                          simp only [typeError, Prod.mk.injEq] at run
                          obtain ⟨_, rfl⟩ := run
                          have lastSafe : last.safeForSpace = true := by simpa using safe
                          simpa using bodyBound (some (.val (value :: more :: rest')))
                            last bodyRun lastSafe
                    | err error =>
                      simp only [Prod.mk.injEq] at run
                      obtain ⟨_, rfl⟩ := run
                      have lastSafe : last.safeForSpace = true := by simpa using safe
                      simpa using bodyBound (some (.err error)) last bodyRun lastSafe

/-- The returning-call dispatch keeps the stack maximum within the limit.
    Flapjack infrastructure for `evaluate_stack_max_le_stack_limit`; no separate
    HOL original. -/
private theorem stackMaxLimitAt_call {C F : Type} (ret : Option (List Nat × NumSet))
    (dest : Option Nat) (names : List Nat) (handler : Option (Nat × DataLang.Prog))
    (state : State C F)
    (bodyIH : ∀ body : DataLang.Prog, ∀ next : State C F, next.clock < state.clock →
      StackMaxLimitAt body next) :
    StackMaxLimitAt (.call ret dest names handler) state := by
  intro res next run safe bound
  simp only [evaluate] at run ⊢
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp [read, typeError] at run ⊢
    obtain ⟨_, rfl⟩ := run
    exact bound
  | some values =>
    simp only [read] at run ⊢
    generalize foundEq : DataSem.findCode dest values state.code state.stackFrameSizes = found
      at run ⊢
    cases found with
    | none =>
      simp [typeError] at run ⊢
      obtain ⟨_, rfl⟩ := run
      exact bound
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      simp only [] at run ⊢
      cases ret with
      | none =>
        simp only [] at run ⊢
        by_cases handlerSome : handler.isSome = true
        · rw [if_pos handlerSome] at run
          simp [typeError] at run ⊢
          obtain ⟨_, rfl⟩ := run
          exact bound
        · rw [if_neg handlerSome] at run
          by_cases zero : state.clock = 0
          · rw [if_pos zero] at run
            simp [timeoutError, flushState] at run ⊢
            obtain ⟨_, rfl⟩ := run
            simpa using bound
          · rw [if_neg zero] at run
            cases bodyRun : evaluate body (DataSem.callEnv args size (decClock state)) with
            | mk bodyRes last =>
              rw [bodyRun] at run
              simp only [] at run
              have bodyBound : ∀ (bodyRes : Option (SemanticPrimitivesHOL.Result
                  (List Value) Value)) (last : State C F),
                  evaluate body (DataSem.callEnv args size (decClock state)) =
                    (bodyRes, last) →
                  last.safeForSpace = true →
                  BackendProps.optionLe last.stackMax (some last.limits.stackLimit) := by
                intro bodyRes last bodyRun lastSafe
                have callSafe := evaluate_safety_of_result body
                  (DataSem.callEnv args size (decClock state)) bodyRes last ⟨bodyRun, lastSafe⟩
                have boundCall : BackendProps.optionLe
                    (DataSem.callEnv args size (decClock state)).stackMax
                    (some (DataSem.callEnv args size (decClock state)).limits.stackLimit) := by
                  simpa only [DataSem.callEnv] using
                    callEnv_stackMax_le args size (decClock state) callSafe
                have clockLt :
                    (DataSem.callEnv args size (decClock state)).clock < state.clock := by
                  simp only [DataSem.callEnv, decClock]
                  omega
                exact bodyIH body (DataSem.callEnv args size (decClock state)) clockLt
                  bodyRes last bodyRun lastSafe boundCall
              cases bodyRes with
              | none =>
                simp only [typeError, Prod.mk.injEq] at run
                obtain ⟨_, rfl⟩ := run
                have lastSafe : last.safeForSpace = true := by simpa using safe
                simpa using bodyBound none last bodyRun lastSafe
              | some value =>
                simp only [Prod.mk.injEq] at run
                obtain ⟨_, rfl⟩ := run
                have lastSafe : last.safeForSpace = true := by simpa using safe
                simpa using bodyBound (some value) last bodyRun lastSafe
      | some retPair =>
        obtain ⟨returns, live⟩ := retPair
        simp only [] at run ⊢
        by_cases nodup : (!returns.Nodup) = true
        · rw [if_pos nodup] at run
          simp [typeError] at run ⊢
          obtain ⟨_, rfl⟩ := run
          exact bound
        · rw [if_neg nodup] at run
          generalize cutEq : DataSem.cutEnv live state.locals = cut at run ⊢
          cases cut with
          | none =>
            simp [typeError] at run ⊢
            obtain ⟨_, rfl⟩ := run
            exact bound
          | some env =>
            simp only [] at run ⊢
            by_cases zero : state.clock = 0
            · rw [if_pos zero] at run
              simp [timeoutError] at run ⊢
              obtain ⟨_, rfl⟩ := run
              have callSafe : (DataSem.callEnv args size
                  (DataSem.pushEnv env handler.isSome (decClock state))).safeForSpace = true := by
                simpa using safe
              simpa only [DataSem.callEnv, DataSem.pushEnv, decClock] using
                callEnv_stackMax_le args size
                  (DataSem.pushEnv env handler.isSome (decClock state)) callSafe
            · rw [if_neg zero] at run
              simp only [fixClock] at run ⊢
              cases bodyRun : evaluate body
                  (DataSem.callEnv args size
                    (DataSem.pushEnv env handler.isSome (decClock state))) with
              | mk bodyRes last =>
                rw [bodyRun] at run
                simp only [] at run
                have bodyBound : ∀ (bodyRes : Option (SemanticPrimitivesHOL.Result
                    (List Value) Value)) (last : State C F),
                    evaluate body (DataSem.callEnv args size
                      (DataSem.pushEnv env handler.isSome (decClock state))) = (bodyRes, last) →
                    last.safeForSpace = true →
                    BackendProps.optionLe last.stackMax (some last.limits.stackLimit) := by
                  intro bodyRes last bodyRun lastSafe
                  have callSafe := evaluate_safety_of_result body
                    (DataSem.callEnv args size
                      (DataSem.pushEnv env handler.isSome (decClock state)))
                    bodyRes last ⟨bodyRun, lastSafe⟩
                  have boundCall : BackendProps.optionLe
                      (DataSem.callEnv args size
                        (DataSem.pushEnv env handler.isSome (decClock state))).stackMax
                      (some (DataSem.callEnv args size
                        (DataSem.pushEnv env handler.isSome
                          (decClock state))).limits.stackLimit) := by
                    simpa only [DataSem.callEnv] using
                      callEnv_stackMax_le args size
                        (DataSem.pushEnv env handler.isSome (decClock state)) callSafe
                  have clockLt :
                      (DataSem.callEnv args size
                        (DataSem.pushEnv env handler.isSome (decClock state))).clock <
                        state.clock := by
                    simp only [DataSem.callEnv, DataSem.pushEnv, decClock]
                    omega
                  exact bodyIH body
                    (DataSem.callEnv args size
                      (DataSem.pushEnv env handler.isSome (decClock state)))
                    clockLt bodyRes last bodyRun lastSafe boundCall
                cases bodyRes with
                | none =>
                  simp only [typeError, Prod.mk.injEq] at run
                  obtain ⟨_, rfl⟩ := run
                  have lastSafe : last.safeForSpace = true := by simpa using safe
                  simpa using bodyBound none last bodyRun lastSafe
                | some result =>
                  cases result with
                  | val vals =>
                    simp only [] at run ⊢
                    by_cases sameLength : vals.length = returns.length
                    · rw [if_pos sameLength] at run
                      cases pop : DataSem.popEnv
                          { last with clock :=
                              (min (DataSem.callEnv args size
                                (DataSem.pushEnv env handler.isSome (decClock state))).clock
                                last.clock) } with
                      | none =>
                        simp only [pop, typeError, Prod.mk.injEq] at run
                        obtain ⟨_, rfl⟩ := run
                        have lastSafe : last.safeForSpace = true := by simpa using safe
                        simpa using bodyBound (some (.val vals)) last bodyRun lastSafe
                      | some popped =>
                        simp only [pop, Prod.mk.injEq] at run
                        obtain ⟨_, rfl⟩ := run
                        have poppedFacts := popEnv_stackMax last
                          (min (DataSem.callEnv args size
                            (DataSem.pushEnv env handler.isSome (decClock state))).clock
                            last.clock) popped pop
                        have lastSafe : last.safeForSpace = true := by
                          have hs := safe
                          simp only [setVars] at hs
                          rw [poppedFacts.2.2] at hs
                          exact hs
                        have poppedBound : BackendProps.optionLe popped.stackMax
                            (some popped.limits.stackLimit) := by
                          rw [poppedFacts.1, poppedFacts.2.1]
                          simpa using bodyBound (some (.val vals)) last bodyRun lastSafe
                        simpa [setVars] using poppedBound
                    · rw [if_neg sameLength] at run
                      simp only [typeError, Prod.mk.injEq] at run
                      obtain ⟨_, rfl⟩ := run
                      have lastSafe : last.safeForSpace = true := by simpa using safe
                      simpa using bodyBound (some (.val vals)) last bodyRun lastSafe
                  | err error =>
                    cases error with
                    | abort reason =>
                      simp only [] at run
                      simp only [Prod.mk.injEq] at run
                      obtain ⟨_, rfl⟩ := run
                      have lastSafe : last.safeForSpace = true := by simpa using safe
                      simpa using bodyBound (some (.err (.abort reason))) last bodyRun lastSafe
                    | raise value =>
                      cases handler with
                      | none =>
                        simp only [] at run
                        simp only [Prod.mk.injEq] at run
                        obtain ⟨_, rfl⟩ := run
                        have lastSafe : last.safeForSpace = true := by simpa using safe
                        simpa using bodyBound (some (.err (.raise value))) last bodyRun lastSafe
                      | some handlerPair =>
                        obtain ⟨name, handlerBody⟩ := handlerPair
                        simp only [] at run
                        let handlerStart : State C F :=
                          setVar name value (clampClock last (min (DataSem.callEnv args size
                            (DataSem.pushEnv env true (decClock state))).clock last.clock))
                        have handlerSafe : handlerStart.safeForSpace = true := by
                          have started := evaluate_safety_of_result handlerBody handlerStart
                            res next ⟨run, safe⟩
                          simpa [handlerStart, setVar, clampClock] using started
                        have lastSafe : last.safeForSpace = true := by
                          have hs := handlerSafe
                          simp only [handlerStart, setVar, clampClock] at hs
                          exact hs
                        have handlerBound : BackendProps.optionLe handlerStart.stackMax
                            (some handlerStart.limits.stackLimit) := by
                          simpa [handlerStart, setVar, clampClock] using
                            bodyBound (some (.err (.raise value))) last bodyRun lastSafe
                        have clockLt : handlerStart.clock < state.clock := by
                          simp only [handlerStart, setVar, clampClock, DataSem.callEnv,
                            DataSem.pushEnv, decClock]
                          omega
                        exact bodyIH handlerBody handlerStart clockLt res next run
                          safe handlerBound

/-- Every safe run keeps the recorded stack maximum within the configured stack
    limit, by induction on the clock and the program size. -/
private theorem stackMaxLimitAt_all {C F : Type} (program : DataLang.Prog)
    (state : State C F) : StackMaxLimitAt program state := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := StackMaxLimitAt) ?_ program state
  intro program state exprIH smaller
  cases program with
  | skip => exact stackMaxLimitAt_skip state
  | move dest src => exact stackMaxLimitAt_move dest src state
  | assign dest op names live => exact stackMaxLimitAt_assign dest op names live state
  | tick => exact stackMaxLimitAt_tick state
  | makeSpace amount names => exact stackMaxLimitAt_makeSpace amount names state
  | raise name => exact stackMaxLimitAt_raise name state
  | «return» names => exact stackMaxLimitAt_return names state
  | seq first second =>
    apply stackMaxLimitAt_seq first second state
    · apply exprIH first state (by omega)
      simp only [DataLang.Prog.seq.sizeOf_spec] at ⊢
      omega
    · intro mid bound
      apply exprIH second mid (by omega)
      simp only [DataLang.Prog.seq.sizeOf_spec] at ⊢
      omega
  | ifThenElse name yes no =>
    apply stackMaxLimitAt_if name yes no state
    · apply exprIH yes state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at ⊢
      omega
    · apply exprIH no state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at ⊢
      omega
  | force ret label src =>
    apply stackMaxLimitAt_force ret label src state
    intro body next bound
    exact smaller body next (by omega)
  | call ret dest names handler =>
    apply stackMaxLimitAt_call ret dest names handler state
    intro body next bound
    exact smaller body next (by omega)

/-- Along a safe run, the recorded stack maximum stays within the configured
    stack limit. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_stack_max_le_stack_limit"]
theorem evaluate_stackMax_le_stackLimit {C F : Type} (program : DataLang.Prog)
    (state : State C F) (res : Option (SemanticPrimitivesHOL.Result (List Value) Value))
    (next : State C F)
    (premises : evaluate program state = (res, next) ∧ next.safeForSpace = true ∧
      BackendProps.optionLe state.stackMax (some state.limits.stackLimit)) :
    BackendProps.optionLe next.stackMax (some next.limits.stackLimit) := by
  obtain ⟨run, safe, bound⟩ := premises
  exact stackMaxLimitAt_all program state res next run safe bound

end Flapjack.Compiler.Backend.DataProps
