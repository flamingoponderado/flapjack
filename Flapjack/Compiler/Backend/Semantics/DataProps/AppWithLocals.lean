module

public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.AppWithClock
public import Flapjack.Misc.MiscThe

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

end Flapjack.Compiler.Backend.DataProps
