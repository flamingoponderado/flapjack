module

public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.AppWithClock
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyAuxFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.NonFfiResources
public import Flapjack.Misc.MiscThe
public import Aesop

@[expose] public section

/-!
# Primitive application under a locals update

The data-language primitive dispatcher reads the locals only through the
auxiliary application stage; the space, limit and stack stages inspect the
heap, limit and stack fields instead.  This module records the field-level
facts needed to commute the dispatcher with a locals update, mirroring
`AppWithClock`'s clock argument stage by stage.
-/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.DataSem
open Classical

/-- HOL's `do_app_safe` Overload (`dataSemScript.sml:1149-1157`): the operation
is admitted, the space stage keeps heap safety, the limit check passes and the
new stack size is below the stack limit.  HOL declares this as an Overload, not
a database declaration, so the definition carries no `@[hol]` tag.  It is
Flapjack infrastructure toward the parked HOL `do_app_with_locals`; no separate
HOL original. -/
noncomputable def doAppSafe {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) : Bool :=
  if allowedOp op values.length then
    doSpaceSafe op values state && decide (limSafe state.limits op values) &&
      miscThe false (Option.map (fun n => decide (state.limits.stackLimit > n))
        (Option.map₂ (· + ·) (stackConsumed state.stackFrameSizes state.limits op values)
          (Option.map₂ (· + ·) (sizeOfStack state.stack) state.localsSize)))
  else false

/-- HOL's `do_app_peak` Overload (`dataSemScript.sml:1160-1163`): installation
and the two comparison operations leave the peak unchanged, every other
operation reports the space stage's peak.  As with `doAppSafe`, HOL declares
this as an Overload, so the definition carries no `@[hol]` tag.  It is
Flapjack infrastructure toward the parked HOL `do_app_with_locals`; no separate
HOL original. -/
noncomputable def doAppPeak {C F : Type} : ClosLang.Op → List Value → State C F → Nat
  | .install, _, state => state.peakHeapLength
  | .intOp .greater, _, state => state.peakHeapLength
  | .intOp .greaterEq, _, state => state.peakHeapLength
  | op, values, state => doSpacePeak op values state

/-- The limit check is a record update of fields other than the locals.
    Flapjack infrastructure toward the parked HOL `do_app_with_locals`; no
    separate HOL original. -/
theorem doLimSafe_locals {C F : Type} (state : State C F) (op : ClosLang.Op)
    (values : List Value) (locals : Spt Value) :
    doLimSafe { state with locals := locals } op values =
      { doLimSafe state op values with locals := locals } := by
  simp [doLimSafe]

/-- Stack accounting is a record update of fields other than the locals.
    Flapjack infrastructure toward the parked HOL `do_app_with_locals`; no
    separate HOL original. -/
theorem doStack_locals {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) (locals : Spt Value) :
    doStack op values { state with locals := locals } =
      { doStack op values state with locals := locals } := by
  simp [doStack]

/-- The space stage leaves the stack, frame sizes, limits, stack maximum and
    locals unchanged.  Flapjack infrastructure toward the parked HOL
    `do_app_with_locals`; no separate HOL original. -/
theorem doSpace_fields {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state next : State C F) (run : doSpace op values state = some next) :
    next.stack = state.stack ∧ next.localsSize = state.localsSize ∧
      next.stackFrameSizes = state.stackFrameSizes ∧ next.limits = state.limits ∧
      next.stackMax = state.stackMax ∧ next.locals = state.locals := by
  unfold doSpace at run
  simp only [] at run
  split at run
  · simp only [Option.some.injEq] at run
    subst next
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split at run
    · simp only [Option.some.injEq] at run
      subst next
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · unfold consumeSpace at run
      split at run
      · simp at run
      · simp only [Option.some.injEq] at run
        subst next
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Installation carries the locals through unchanged.  Flapjack infrastructure
    toward the parked HOL `do_app_with_locals`; no separate HOL original. -/
theorem doInstall_locals {C F R : Type} (args : List Value) (state : State C F)
    (locals : Spt Value) :
    doInstall args { state with locals := locals } =
      mapResult (fun ((value, next) : Value × State C F) =>
          (value, { next with locals := locals })) (id : R → R)
        (doInstall args state) := by
  simp only [doInstall, mapResult, mapErrorResult]
  repeat' (split <;> try rfl)

/-- The space stage reports the source's post-reset safety observation.
    Flapjack infrastructure toward the parked HOL `do_app_with_locals`; no
    separate HOL original. -/
theorem doSpace_safeForSpace {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state next : State C F) (run : doSpace op values state = some next) :
    next.safeForSpace = doSpaceSafe op values state := by
  by_cases reset : DataLang.opSpaceReset op
  · simp only [doSpace] at run
    rw [if_pos reset] at run
    simp only [Option.some.injEq] at run
    subst next
    simp only [doSpaceSafe]
    rw [if_pos reset]
  · by_cases req : DataSpace.opSpaceReq op values.length = 0
    · simp only [doSpace] at run
      rw [if_neg reset, if_pos req] at run
      simp only [Option.some.injEq] at run
      subst next
      simp only [doSpaceSafe]
      rw [if_neg reset]
    · simp only [doSpace] at run
      rw [if_neg reset, if_neg req] at run
      unfold consumeSpace at run
      by_cases fits : state.space < DataSpace.opSpaceReq op values.length
      · rw [if_pos fits] at run
        cases run
      · rw [if_neg fits] at run
        simp only [Option.some.injEq] at run
        subst next
        simp only [doSpaceSafe]
        rw [if_neg reset]

/-- The space stage reports the source's post-reset peak-heap estimate.
    Flapjack infrastructure toward the parked HOL `do_app_with_locals`; no
    separate HOL original. -/
theorem doSpace_peakHeapLength {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state next : State C F) (run : doSpace op values state = some next) :
    next.peakHeapLength = doSpacePeak op values state := by
  by_cases reset : DataLang.opSpaceReset op
  · simp only [doSpace] at run
    rw [if_pos reset] at run
    simp only [Option.some.injEq] at run
    subst next
    simp only [doSpacePeak]
    rw [if_pos reset]
  · by_cases req : DataSpace.opSpaceReq op values.length = 0
    · simp only [doSpace] at run
      rw [if_neg reset, if_pos req] at run
      simp only [Option.some.injEq] at run
      subst next
      simp only [doSpacePeak]
      rw [if_neg reset]
    · simp only [doSpace] at run
      rw [if_neg reset, if_neg req] at run
      unfold consumeSpace at run
      by_cases fits : state.space < DataSpace.opSpaceReq op values.length
      · rw [if_pos fits] at run
        cases run
      · rw [if_neg fits] at run
        simp only [Option.some.injEq] at run
        subst next
        simp only [doSpacePeak]
        rw [if_neg reset]

/-- The space stage depends on the locals only through its safety and peak
    observations: replacing the locals replaces those two fields and the locals
    themselves, and keeps the option's shape.  Flapjack infrastructure toward
    the parked HOL `do_app_with_locals`; no separate HOL original. -/
theorem doSpace_locals_eq {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) (locals : Spt Value) :
    doSpace op values { state with locals := locals } =
      (doSpace op values state).map (fun next =>
        { next with
          locals := locals,
          safeForSpace := doSpaceSafe op values { state with locals := locals },
          peakHeapLength := doSpacePeak op values { state with locals := locals } }) := by
  by_cases reset : DataLang.opSpaceReset op
  · simp only [doSpace, doSpaceSafe, doSpacePeak, if_pos reset, Option.map_some]
  · by_cases req : DataSpace.opSpaceReq op values.length = 0
    · simp only [doSpace, doSpaceSafe, doSpacePeak, if_neg reset, if_pos req, Option.map_some]
    · simp only [doSpace, doSpaceSafe, doSpacePeak, if_neg reset, if_neg req]
      unfold consumeSpace
      by_cases fits : state.space < DataSpace.opSpaceReq op values.length
      · simp only [if_pos fits, Option.map_none]
      · simp only [if_neg fits, Option.map_some]

/-- Do-notation builds an `Option` bind through the `Bind` instance, so
    `Option.bind_eq_some_iff` does not match it syntactically.  This bridge
    lets the auxiliary-stage case analysis destruct those binds.  Flapjack
    infrastructure toward the parked HOL `do_app_with_locals`; no separate HOL
    original. -/
theorem bind_eq_optionBind {α β : Type} (o : Option α) (f : α → Option β) :
    Bind.bind o f = Option.bind o f := rfl

/-- A successful non-FFI application cannot turn an unsafe state safe: safety
    is only ever conjoined, never restored.  It is one half of the auxiliary
    stage's safety accounting needed by the parked HOL `do_app_with_locals`; no
    separate HOL original. -/
theorem applyNonFfi_safeForSpace_of_false {C F : Type} (op : ClosLang.Op)
    (values : List Value) (state next : State C F) (value : Value)
    (run : applyNonFfi op values state = some (value, next))
    (hsafe : state.safeForSpace = false) :
    next.safeForSpace = false := by
  have mono := (applyNonFfi_successFields op values state next value true run).2.2
  cases hnext : next.safeForSpace
  · rfl
  · rw [hsafe] at mono
    exact Bool.noConfusion (mono hnext)

/-- The FFI branch of the auxiliary dispatcher leaves the safety flag as it
    found it, so a successful FFI call cannot make an unsafe state safe.
    Flapjack infrastructure toward the parked HOL `do_app_with_locals`; no
    separate HOL original. -/
private theorem doAppAuxFfi_safeForSpace_of_false {C F : Type}
    (name : Basis.Pure.MlString.MlString) (values : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.ffi name) values state = .val (value, next))
    (hsafe : state.safeForSpace = false) :
    next.safeForSpace = false := by
  rcases values with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;>
    simp only [doAppAux] at run ⊢
  all_goals repeat' (first | split at run | simp_all)
  all_goals rcases run with ⟨_, rfl⟩
  all_goals simp

/-- A successful auxiliary application cannot turn an unsafe state safe: every
    branch either keeps the flag or conjoins a further test with it, and the FFI
    branch keeps it unchanged.  Together with the limit-check bound this is the
    auxiliary half of HOL `do_app_safe`'s accounting.  Flapjack infrastructure
    toward the parked HOL `do_app_with_locals`; no separate HOL original. -/
theorem doAppAux_safeForSpace_of_false {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux op values state = .val (value, next))
    (hsafe : state.safeForSpace = false) :
    next.safeForSpace = false := by
  cases op with
  | ffi name => exact doAppAuxFfi_safeForSpace_of_false name values state next value run hsafe
  | install =>
    rcases values with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;>
      simp only [doAppAux] at run ⊢
    all_goals repeat' (first | split at run | simp_all [applyNonFfi])
  | intOp op' =>
    cases h : applyNonFfi (.intOp op') values state with
    | none =>
      simp only [doAppAux, h] at run
      cases run
    | some pair =>
      simp only [doAppAux, h] at run
      injection run with hp
      rw [hp] at h
      exact applyNonFfi_safeForSpace_of_false (.intOp op') values state next value h hsafe
  | wordOp op' =>
    cases h : applyNonFfi (.wordOp op') values state with
    | none =>
      simp only [doAppAux, h] at run
      cases run
    | some pair =>
      simp only [doAppAux, h] at run
      injection run with hp
      rw [hp] at h
      exact applyNonFfi_safeForSpace_of_false (.wordOp op') values state next value h hsafe
  | label l =>
    cases h : applyNonFfi (.label l) values state with
    | none =>
      simp only [doAppAux, h] at run
      cases run
    | some pair =>
      simp only [doAppAux, h] at run
      injection run with hp
      rw [hp] at h
      exact applyNonFfi_safeForSpace_of_false (.label l) values state next value h hsafe
  | thunkOp op' =>
    cases h : applyNonFfi (.thunkOp op') values state with
    | none =>
      simp only [doAppAux, h] at run
      cases run
    | some pair =>
      simp only [doAppAux, h] at run
      injection run with hp
      rw [hp] at h
      exact applyNonFfi_safeForSpace_of_false (.thunkOp op') values state next value h hsafe
  | globOp op' =>
    cases h : applyNonFfi (.globOp op') values state with
    | none =>
      simp only [doAppAux, h] at run
      cases run
    | some pair =>
      simp only [doAppAux, h] at run
      injection run with hp
      rw [hp] at h
      exact applyNonFfi_safeForSpace_of_false (.globOp op') values state next value h hsafe
  | blockOp op' =>
    cases h : applyNonFfi (.blockOp op') values state with
    | none =>
      simp only [doAppAux, h] at run
      cases run
    | some pair =>
      simp only [doAppAux, h] at run
      injection run with hp
      rw [hp] at h
      exact applyNonFfi_safeForSpace_of_false (.blockOp op') values state next value h hsafe
  | memOp op' =>
    cases h : applyNonFfi (.memOp op') values state with
    | none =>
      simp only [doAppAux, h] at run
      cases run
    | some pair =>
      simp only [doAppAux, h] at run
      injection run with hp
      rw [hp] at h
      exact applyNonFfi_safeForSpace_of_false (.memOp op') values state next value h hsafe

/-- Successful auxiliary application keeps its value when only the safety
    flag is replaced, recording the new flag existentially.  Flapjack
    infrastructure toward the parked HOL `do_app_with_locals`; no separate HOL
    original. -/
private theorem doAppAux_safeSuccess' {C F : Type} (op : ClosLang.Op)
    (values : List Value) (state next : State C F) (value : Value) (safe : Bool)
    (run : doAppAux op values state = .val (value, next)) :
    ∃ safe', doAppAux op values { state with safeForSpace := safe } =
      .val (value, { next with safeForSpace := safe' }) := by
  simp only [doAppAux] at run ⊢
  all_goals repeat' (split at run <;> simp_all)
  all_goals try (obtain ⟨safe', result⟩ :=
    (applyNonFfi_successFields _ _ state next value safe (by assumption)).1; simp_all)
  all_goals try aesop

/-- Successful auxiliary application keeps its value, its stack maximum and its
    peak-heap estimate when those fields and the safety flag are replaced.
    Flapjack infrastructure toward the parked HOL `do_app_with_locals`; no
    separate HOL original. -/
private theorem doAppAux_safePeakStackMax' {C F : Type} (op : ClosLang.Op)
    (values : List Value) (state next : State C F) (value : Value) (safe : Bool)
    (mx : Option Nat) (peak : Nat)
    (run : doAppAux op values state = .val (value, next)) :
    ∃ safe', doAppAux op values
        { state with
          safeForSpace := safe
          stackMax := mx
          peakHeapLength := peak } =
      .val (value, { next with
        safeForSpace := safe'
        stackMax := mx
        peakHeapLength := peak }) := by
  obtain ⟨safe', safeChange⟩ := doAppAux_safeSuccess' op values state next value safe run
  have fields := doAppAux_withFields op values { state with safeForSpace := safe }
    state.stack state.localsSize mx peak state.locals state.space state.handler state.clock
    state.stackFrameSizes state.compile
  rw [safeChange] at fields
  refine ⟨safe', ?_⟩
  obtain ⟨stackEq, localsSizeEq, _, _, localsEq, spaceEq, handlerEq, clockEq, frameSizesEq,
    compileEq⟩ := doAppAux_fieldFrame op values state next value run
  simpa [Flapjack.SemanticPrimitivesProps.mapResult, stackEq, localsSizeEq, localsEq, spaceEq,
    handlerEq, clockEq, frameSizesEq, compileEq] using fields

/-- Successful auxiliary application keeps its value when the locals, the
    safety flag, the stack maximum and the peak-heap estimate are replaced.
    Flapjack infrastructure toward the parked HOL `do_app_with_locals`; no
    separate HOL original. -/
private theorem doAppAux_changeFields' {C F : Type} (op : ClosLang.Op)
    (values : List Value) (state next : State C F) (value : Value) (locals : Spt Value)
    (safe : Bool) (mx : Option Nat) (peak : Nat)
    (run : doAppAux op values state = .val (value, next)) :
    ∃ safe', doAppAux op values
        { state with
          locals := locals
          safeForSpace := safe
          stackMax := mx
          peakHeapLength := peak } =
      .val (value, { next with
        locals := locals
        safeForSpace := safe'
        stackMax := mx
        peakHeapLength := peak }) := by
  obtain ⟨safe', first⟩ :=
    doAppAux_safePeakStackMax' op values state next value safe mx peak run
  have second := doAppAux_withLocals op values
    { state with safeForSpace := safe, stackMax := mx, peakHeapLength := peak } locals
  rw [first] at second
  refine ⟨safe', ?_⟩
  have key :
      { state with
        locals := locals
        safeForSpace := safe
        stackMax := mx
        peakHeapLength := peak } =
      { { state with
          safeForSpace := safe
          stackMax := mx
          peakHeapLength := peak } with
        locals := locals } := rfl
  rw [key]
  simpa [Flapjack.SemanticPrimitivesProps.mapResult] using second

/-- A non-admitted operation consumes no stack.  Flapjack infrastructure
    toward the parked HOL `do_app_with_locals`; no separate HOL original. -/
theorem stackConsumed_none {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) (h : ¬ allowedOp op values.length) :
    stackConsumed state.stackFrameSizes state.limits op values = none := by
  unfold stackConsumed
  split
  all_goals first | rw [if_neg h] | simp_all [allowedOp]

/-- The limit and stack stages install exactly the source's safety observation:
    after `doLimSafe` and `doStack` the flag equals `doAppSafe` at the source
    state.  Flapjack infrastructure toward the parked HOL `do_app_with_locals`;
    no separate HOL original. -/
theorem doStack_doLimSafe_safeForSpace {C F : Type} (op : ClosLang.Op)
    (values : List Value) (state space : State C F)
    (run : doSpace op values state = some space) :
    (doStack op values (doLimSafe space op values)).safeForSpace =
      doAppSafe op values state := by
  obtain ⟨hstack, hlocalsSize, hframes, hlimits, _, _⟩ :=
    doSpace_fields op values state space run
  have hsafe := doSpace_safeForSpace op values state space run
  unfold doStack doLimSafe doAppSafe
  rw [hstack, hlocalsSize, hframes, hlimits, hsafe]
  by_cases hallowed : allowedOp op values.length
  · rw [if_pos hallowed]
    simp only [Bool.and_assoc, Bool.and_comm]
    cases ho : (Option.map (fun n => decide (state.limits.stackLimit > n))
      (Option.map₂ (fun x1 x2 => x1 + x2)
        (stackConsumed state.stackFrameSizes state.limits op values)
        (Option.map₂ (fun x1 x2 => x1 + x2) (sizeOfStack state.stack)
          state.localsSize))) <;>
      simp [miscThe, Option.getD]
  · rw [if_neg hallowed]
    rw [stackConsumed_none op values state hallowed]
    simp

end Flapjack.Compiler.Backend.DataProps
