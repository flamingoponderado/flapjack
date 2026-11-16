module

public import Flapjack.Compiler.Backend.Semantics.DataProps.CcCoOnlyDiff
public import Flapjack.Compiler.Backend.Semantics.DataProps.AppWithClock

@[expose] public section

/-!
# Primitive application under a compiler-configuration change

`ccCoOnlyDiff` compares the sixteen runtime fields of two states and leaves
`compile` and `compileOracle` free, so the compared states may have different
compiler types. Every stage of the primitive dispatcher except installation
reads only those sixteen fields. The lemmas below rebuild a state of the target
compiler type from a source state, taking the compiler configuration from the
target, and show that each stage commutes with that rebuild.
-/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.DataSem

/-- Rebuild a state of compiler type `C2` from a `C1` state, taking the
compiler callback and oracle from a `C2` state. -/
abbrev castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) : State C2 F :=
  { locals := s.locals
    localsSize := s.localsSize
    stack := s.stack
    stackMax := s.stackMax
    stackFrameSizes := s.stackFrameSizes
    global := s.global
    handler := s.handler
    refs := s.refs
    compile := t.compile
    clock := s.clock
    code := s.code
    ffi := s.ffi
    space := s.space
    tstamps := s.tstamps
    limits := s.limits
    safeForSpace := s.safeForSpace
    peakHeapLength := s.peakHeapLength
    compileOracle := t.compileOracle }

/-- The rebuilt state agrees with its source on every compared field. -/
theorem ccCoOnlyDiff_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    ccCoOnlyDiff s (castCompiler s t) := by
  simp [ccCoOnlyDiff]

/-- The agreement relation is exactly the statement that rebuilding the source
with the target's compiler configuration gives the target. -/
theorem ccCoOnlyDiff_iff_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    ccCoOnlyDiff s t ↔ castCompiler s t = t := by
  constructor
  · intro diff
    obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handler, refs, clock, code,
      ffi, space, tstamps, limits, safe, peak⟩ := diff
    cases t
    simp_all [castCompiler]
  · intro same
    rw [← same]
    exact ccCoOnlyDiff_castCompiler s t

/-- Rebuilding a state from itself is inert. -/
theorem castCompiler_id {C F : Type} (s : State C F) :
    castCompiler s s = s := by
  simp [castCompiler]

/-- The space requirement of an operation reads only the limits. -/
theorem spaceConsumed_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (op : ClosLang.Op) (values : List DataSem.Value) :
    spaceConsumed (castCompiler s t) op values = spaceConsumed s op values := rfl

/-- The heap reachable from the roots reads only the heap fields. -/
theorem sizeOfHeap_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    sizeOfHeap (castCompiler s t) = sizeOfHeap s := rfl

/-- The heap reachable from arguments reads only the heap fields. -/
theorem sizeOfHeapArgs_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (values : List DataSem.Value) :
    sizeOfHeapArgs values (castCompiler s t) = sizeOfHeapArgs values s := rfl

/-- Thunk-freedom of the heap reads only the references. -/
theorem noThunksInRefs_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    noThunksInRefs (castCompiler s t).refs ↔ noThunksInRefs s.refs := by
  rfl

/-- Space consumption reads only the space field. -/
theorem consumeSpace_castCompiler {C1 C2 F : Type} (amount : Nat) (s : State C1 F)
    (t : State C2 F) :
    consumeSpace amount (castCompiler s t) =
      (consumeSpace amount s).map (fun next => castCompiler next t) := by
  simp only [consumeSpace, castCompiler]
  by_cases short : s.space < amount
  · simp only [short, if_true, Option.map_none]
  · simp only [short, if_false, Option.map_some]

/-- The space stage commutes with the rebuild. -/
theorem doSpace_castCompiler {C1 C2 F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (s : State C1 F) (t : State C2 F) :
    doSpace op values (castCompiler s t) =
      (doSpace op values s).map (fun next => castCompiler next t) := by
  simp only [doSpace, castCompiler]
  by_cases reset : DataLang.opSpaceReset op = true
  · simp only [reset, if_true, Option.map_some]
    rfl
  · simp only [reset]
    by_cases req : DataSpace.opSpaceReq op values.length = 0
    · simp only [req, if_true]
      rfl
    · simp only [req, if_false]
      exact consumeSpace_castCompiler _ _ _

/-- The limit check reads only the limits and the safety flag. -/
theorem doLimSafe_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (op : ClosLang.Op) (values : List DataSem.Value) :
    doLimSafe (castCompiler s t) op values = castCompiler (doLimSafe s op values) t := rfl

/-- The length check reads only the limits and the safety flag. -/
theorem checkLim_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (length : Nat) :
    checkLim (castCompiler s t) length = castCompiler (checkLim s length) t := rfl

/-- Stack requirements read only the frame sizes and the limits. -/
theorem stackConsumed_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (op : ClosLang.Op) (values : List DataSem.Value) :
    stackConsumed (castCompiler s t).stackFrameSizes (castCompiler s t).limits op values =
      stackConsumed s.stackFrameSizes s.limits op values := rfl

/-- The stack size reads only the stack. -/
theorem sizeOfStack_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    sizeOfStack (castCompiler s t).stack = sizeOfStack s.stack := rfl

/-- The stack stage commutes with the rebuild. -/
theorem doStack_castCompiler {C1 C2 F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (s : State C1 F) (t : State C2 F) :
    doStack op values (castCompiler s t) = castCompiler (doStack op values s) t := rfl

/-- A fresh-timestamp allocation with a length check commutes with the
rebuild, since both the timestamp field and the length check are compared. -/
theorem withFreshTimestamp_castCompiler {C1 C2 F : Type} (s : State C1 F)
    (t : State C2 F) (count length : Nat) (value : Nat → DataSem.Value) :
    withFreshTimestamp (castCompiler s t) count
        (fun ts next => some (value ts, checkLim next length)) =
      (withFreshTimestamp s count
        (fun ts next => some (value ts, checkLim next length))).map
        (fun pair => (pair.1, castCompiler pair.2 t)) := by
  simp only [withFreshTimestamp, castCompiler]
  cases h : s.tstamps with
  | none => simp only [h, Option.map_some, checkLim]
  | some ts => simp only [Option.map_some, checkLim]

/-- Non-FFI primitive application commutes with the rebuild. -/
theorem applyNonFfi_castCompiler {C1 C2 F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (s : State C1 F) (t : State C2 F) :
    applyNonFfi op values (castCompiler s t) =
      (applyNonFfi op values s).map (fun pair => (pair.1, castCompiler pair.2 t)) := by
  simp only [applyNonFfi, castCompiler]
  all_goals repeat' (first | split | split)
  all_goals simp_all [Option.map_map, Function.comp_def]
  all_goals
    repeat' (first
      | apply Option.bind_congr
      | intro a _
      | split
      | rfl
      | simp_all [Option.map_bind, withFreshTimestamp_castCompiler])

/-- A successful mapped application corresponds to mapping the result. -/
theorem mapResult_of_optionMap {C1 C2 F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (s : State C1 F) (t : State C2 F) :
    ((match Option.map (fun pair => (pair.1, castCompiler pair.2 t))
        (applyNonFfi op values s) with
      | some pair => Result.val pair
      | none => Result.err (.abort .typeError)) :
      Result (DataSem.Value × State C2 F) DataSem.Value) =
    mapResult (fun pair => (pair.1, castCompiler pair.2 t)) id
      ((match applyNonFfi op values s with
        | some pair => Result.val pair
        | none => Result.err (.abort .typeError)) :
        Result (DataSem.Value × State C1 F) DataSem.Value) := by
  cases h : applyNonFfi op values s with
  | none => rfl
  | some pair => rfl

/-- The auxiliary dispatcher commutes with the rebuild, including FFI calls. -/
theorem doAppAux_castCompiler {C1 C2 F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (s : State C1 F) (t : State C2 F) :
    doAppAux op values (castCompiler s t) =
      mapResult (fun pair => (pair.1, castCompiler pair.2 t)) id (doAppAux op values s) := by
  cases op with
  | ffi name =>
    simp only [doAppAux]
    all_goals repeat' (first | split | split)
    all_goals simp_all [mapResult, mapErrorResult]
  | install =>
    simp only [doAppAux]
    rw [applyNonFfi_castCompiler]
    exact mapResult_of_optionMap ClosLang.Op.install values s t
  | intOp op' =>
    simp only [doAppAux]
    rw [applyNonFfi_castCompiler]
    exact mapResult_of_optionMap (ClosLang.Op.intOp op') values s t
  | label label =>
    simp only [doAppAux]
    rw [applyNonFfi_castCompiler]
    exact mapResult_of_optionMap (ClosLang.Op.label label) values s t
  | thunkOp op' =>
    simp only [doAppAux]
    rw [applyNonFfi_castCompiler]
    exact mapResult_of_optionMap (ClosLang.Op.thunkOp op') values s t
  | globOp op' =>
    simp only [doAppAux]
    rw [applyNonFfi_castCompiler]
    exact mapResult_of_optionMap (ClosLang.Op.globOp op') values s t
  | blockOp op' =>
    simp only [doAppAux]
    rw [applyNonFfi_castCompiler]
    exact mapResult_of_optionMap (ClosLang.Op.blockOp op') values s t
  | memOp op' =>
    simp only [doAppAux]
    rw [applyNonFfi_castCompiler]
    exact mapResult_of_optionMap (ClosLang.Op.memOp op') values s t
  | wordOp op' =>
    simp only [doAppAux]
    rw [applyNonFfi_castCompiler]
    exact mapResult_of_optionMap (ClosLang.Op.wordOp op') values s t

/-- The non-install dispatcher branch commutes with the rebuild. -/
theorem doAppOther_castCompiler {C1 C2 F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (s : State C1 F) (t : State C2 F) :
    doAppOther op values (castCompiler s t) =
      mapResult (fun pair => (pair.1, castCompiler pair.2 t)) id
        (doAppOther op values s) := by
  simp only [doAppOther]
  cases space : doSpace op values s with
  | none =>
    rw [doSpace_castCompiler, space]
    simp only [Option.map_none, mapResult, mapErrorResult]
  | some next =>
    rw [doSpace_castCompiler, space, Option.map_some]
    dsimp only
    rw [doLimSafe_castCompiler, doStack_castCompiler, doAppAux_castCompiler]

/-- A successful installation always clears the safety flag. -/
theorem doInstall_safeForSpace_false {C F R : Type} (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F)
    (run : doInstall (R := R) args state = .val (value, next)) :
    next.safeForSpace = false := by
  simp only [doInstall] at run
  repeat' (split at run)
  all_goals
    first
    | obtain ⟨_, rfl⟩ := run
      rfl
    | simp_all

/-- The dispatcher commutes with the rebuild away from installation. -/
theorem doApp_castCompiler_noninstall {C1 C2 F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (s : State C1 F) (t : State C2 F)
    (ne : op ≠ .install) :
    doApp op values (castCompiler s t) =
      mapResult (fun pair => (pair.1, castCompiler pair.2 t)) id
        (doApp op values s) := by
  cases op with
  | install => exact absurd rfl ne
  | intOp op' =>
    cases op' with
    | greater => simp only [doApp, mapResult, mapErrorResult]
    | greaterEq => simp only [doApp, mapResult, mapErrorResult]
    | const a => exact doAppOther_castCompiler (.intOp (.const a)) values s t
    | add => exact doAppOther_castCompiler (.intOp .add) values s t
    | sub => exact doAppOther_castCompiler (.intOp .sub) values s t
    | mult => exact doAppOther_castCompiler (.intOp .mult) values s t
    | div => exact doAppOther_castCompiler (.intOp .div) values s t
    | mod => exact doAppOther_castCompiler (.intOp .mod) values s t
    | less => exact doAppOther_castCompiler (.intOp .less) values s t
    | lessEq => exact doAppOther_castCompiler (.intOp .lessEq) values s t
    | lessConstSmall n => exact doAppOther_castCompiler (.intOp (.lessConstSmall n)) values s t
  | label label => exact doAppOther_castCompiler (.label label) values s t
  | ffi name => exact doAppOther_castCompiler (.ffi name) values s t
  | thunkOp op' => exact doAppOther_castCompiler (.thunkOp op') values s t
  | globOp op' => exact doAppOther_castCompiler (.globOp op') values s t
  | blockOp op' => exact doAppOther_castCompiler (.blockOp op') values s t
  | memOp op' => exact doAppOther_castCompiler (.memOp op') values s t
  | wordOp op' => exact doAppOther_castCompiler (.wordOp op') values s t

/-- Exact HOL `do_app_cc_co_only_diff_rval`
(`dataPropsScript.sml:2993`): a successful application at a safe state has a
successful counterpart in any state agreeing on the sixteen compared fields,
and the two results agree on those fields. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_cc_co_only_diff_rval"]
theorem doApp_ccCoOnlyDiff_rval {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (op : ClosLang.Op) (values : List DataSem.Value) (value : DataSem.Value)
    (next : State C1 F)
    (premises : doApp op values s = .val (value, next) ∧ next.safeForSpace = true ∧
      ccCoOnlyDiff s t) :
    ∃ t1, doApp op values t = .val (value, t1) ∧ ccCoOnlyDiff next t1 := by
  obtain ⟨run, safe, diff⟩ := premises
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  cases op with
  | install =>
    simp only [doApp] at run
    have cleared := doInstall_safeForSpace_false values _ value next run
    rw [cleared] at safe
    simp at safe
  | intOp op' =>
    refine ⟨castCompiler next t, ?_, ccCoOnlyDiff_castCompiler next t⟩
    rw [doApp_castCompiler_noninstall (.intOp op') values s t (by simp), run]
    simp only [mapResult]
  | label label =>
    refine ⟨castCompiler next t, ?_, ccCoOnlyDiff_castCompiler next t⟩
    rw [doApp_castCompiler_noninstall (.label label) values s t (by simp), run]
    simp only [mapResult]
  | ffi name =>
    refine ⟨castCompiler next t, ?_, ccCoOnlyDiff_castCompiler next t⟩
    rw [doApp_castCompiler_noninstall (.ffi name) values s t (by simp), run]
    simp only [mapResult]
  | thunkOp op' =>
    refine ⟨castCompiler next t, ?_, ccCoOnlyDiff_castCompiler next t⟩
    rw [doApp_castCompiler_noninstall (.thunkOp op') values s t (by simp), run]
    simp only [mapResult]
  | globOp op' =>
    refine ⟨castCompiler next t, ?_, ccCoOnlyDiff_castCompiler next t⟩
    rw [doApp_castCompiler_noninstall (.globOp op') values s t (by simp), run]
    simp only [mapResult]
  | blockOp op' =>
    refine ⟨castCompiler next t, ?_, ccCoOnlyDiff_castCompiler next t⟩
    rw [doApp_castCompiler_noninstall (.blockOp op') values s t (by simp), run]
    simp only [mapResult]
  | memOp op' =>
    refine ⟨castCompiler next t, ?_, ccCoOnlyDiff_castCompiler next t⟩
    rw [doApp_castCompiler_noninstall (.memOp op') values s t (by simp), run]
    simp only [mapResult]
  | wordOp op' =>
    refine ⟨castCompiler next t, ?_, ccCoOnlyDiff_castCompiler next t⟩
    rw [doApp_castCompiler_noninstall (.wordOp op') values s t (by simp), run]
    simp only [mapResult]

/-- Exact HOL `do_app_cc_co_only_diff_rerr`
(`dataPropsScript.sml:3028`): a failing application away from installation
fails with the same error in any state agreeing on the sixteen compared
fields. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_cc_co_only_diff_rerr"]
theorem doApp_ccCoOnlyDiff_rerr {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (op : ClosLang.Op) (values : List DataSem.Value) (error : ErrorResult DataSem.Value)
    (premises : doApp op values s = .err error ∧ op ≠ .install ∧ ccCoOnlyDiff s t) :
    doApp op values t = .err error := by
  obtain ⟨run, ne, diff⟩ := premises
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same, doApp_castCompiler_noninstall op values s t ne, run]
  simp only [mapResult]
  cases error <;> rfl

end Flapjack.Compiler.Backend.DataProps
