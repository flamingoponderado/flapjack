import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveAll
import Flapjack.Compiler.Backend.Semantics.DataProps.HeapSwap

/-! Primitive success under resource-field updates. The proof reuses the
liveness pass's primitive cases; those cases must remain independent of this
module to avoid an import cycle. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.DataLive

/-- Assemble the existing liveness primitive cases. This is proof infrastructure. -/
private theorem auxRelation {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.Op) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux op args source) (doAppAux op args target) := by
  cases op with
  | blockOp op => exact stateRel_doAppAux_block source target live op args related
  | memOp op => exact stateRel_doAppAux_memory source target live op args related
  | globOp op => exact stateRel_doAppAux_global source target live op args related
  | ffi name => exact stateRel_doAppAux_ffi source target live name args related
  | thunkOp op => exact stateRel_doAppAux_thunk source target live op args related
  | intOp op =>
    cases h : doIntApp op args <;> simp [doAppAux_int_exact, h, appRel, related]
  | wordOp op =>
    cases h : doWordApp op args <;> simp [doAppAux_word_exact, h, appRel, related]
  | label label =>
    have code := related.1
    cases args with
    | nil => cases found : (sptLookup label source.code).isSome <;> simp [doAppAux, applyNonFfi, appRel, ← code, found, related]
    | cons first rest => simp [doAppAux, applyNonFfi, appRel]
  | install => simp [doAppAux, applyNonFfi, appRel]
/-- Successful auxiliary applications preserve local control fields. -/
private theorem auxControl {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux op args state = .val (value, next)) : SameLocalControl state next := by
  cases op with
  | label label => exact doAppAux_label_frame label args state next value run
  | ffi name => exact doAppAux_ffi_frame name args state next value run
  | intOp op => exact doAppAux_int_frame op args state next value run
  | wordOp op => exact doAppAux_word_frame op args state next value run
  | blockOp op => exact doAppAux_block_frame op args state next value run
  | globOp op => exact doAppAux_global_frame op args state next value run
  | memOp op => exact doAppAux_mem_frame op args state next value run
  | thunkOp op => exact doAppAux_thunk_frame op args state next value run
  | install => simp [doAppAux, applyNonFfi] at run

/-- Auxiliary primitive success is preserved by updating resource fields. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_sm_safe_peak_swap"]
theorem doAppAux_stackSafePeakSwap {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : doAppAux op args state = .val (value, next)) :
    ∃ safe' peak' mx', doAppAux op args {state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak} =
      .val (value, {next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak'}) := by
  let target := {state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx}
  have related : stateRel state target .ln := by simp [stateRel, target]
  have simulation := auxRelation state target .ln op args related
  rw [run] at simulation
  cases targetRun : doAppAux op args target with
  | err e => simp [appRel, targetRun] at simulation
  | val pair =>
    obtain ⟨otherValue, otherNext⟩ := pair
    simp [appRel, targetRun] at simulation
    obtain ⟨rfl, nextRel⟩ := simulation
    have left := auxControl op args state next value run
    have right := auxControl op args target otherNext value targetRun
    have same : otherNext = {next with safeForSpace := otherNext.safeForSpace, peakHeapLength := otherNext.peakHeapLength, stackMax := otherNext.stackMax} := by
      rcases nextRel with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
      cases next
      cases otherNext
      simp_all [SameLocalControl, target]
    refine ⟨otherNext.safeForSpace, otherNext.peakHeapLength, otherNext.stackMax, ?_⟩
    rw [← same]

/-- The successful space-and-auxiliary path preserves the returned value
under resource updates. This is proof infrastructure for the HOL swap. -/
private theorem appSpace_success {C F : Type} (op : ClosLang.Op)
    (args : List DataSem.Value) (state : State C F) (value : DataSem.Value) (next : State C F)
    (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : (match doSpace op args state with
      | none => Result.err (.abort .typeError)
      | some accounted => doAppAux op args (doStack op args (doLimSafe accounted op args))) = .val (value, next)) :
    ∃ safe' peak' mx',
      (match doSpace op args { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak } with
      | none => Result.err (.abort .typeError)
      | some accounted => doAppAux op args (doStack op args (doLimSafe accounted op args))) =
        .val (value, { next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak' }) := by
  cases source : doSpace op args state with
  | none => simp [source] at run
  | some accounted =>
    have appRun : doAppAux op args (doStack op args (doLimSafe accounted op args)) = .val (value, next) := by
      simpa [source] using run
    obtain ⟨safe', peak', mx', target⟩ := doSpace_some_resource op args state accounted safe peak mx source
    obtain ⟨safe'', peak'', mx'', account⟩ := doStack_doLimSafe_resource op args accounted safe' peak' mx'
    obtain ⟨safe''', peak''', mx''', result⟩ := doAppAux_stackSafePeakSwap op args
      (doStack op args (doLimSafe accounted op args)) value next mx'' safe'' peak'' appRun
    exact ⟨safe''', peak''', mx''', by simpa only [target, account] using result⟩

/-- Primitive success is preserved by updating resource fields. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_sm_safe_peak_swap"]
theorem doApp_stackSafePeakSwap {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : doApp op args state = .val (value, next)) :
    ∃ safe' peak' mx', doApp op args { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak } =
      .val (value, { next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak' }) := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    have equation := doInstall_safePeak (R := DataSem.Value) args
      { state with stackMax := none, stackFrameSizes := .ln } safe peak
    rw [run] at equation
    refine ⟨next.safeForSpace, peak, next.stackMax, ?_⟩
    simpa using equation
  | intOp intop =>
    have normal := appSpace_success (.intOp intop) args state value next mx safe peak
    cases intop <;> simp only [doApp] at run ⊢
    all_goals first | exact normal run | contradiction
  | label label =>
    simp only [doApp] at run ⊢
    exact appSpace_success (.label label) args state value next mx safe peak run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact appSpace_success (.ffi name) args state value next mx safe peak run
  | wordOp wordop =>
    simp only [doApp] at run ⊢
    exact appSpace_success (.wordOp wordop) args state value next mx safe peak run
  | blockOp blockop =>
    simp only [doApp] at run ⊢
    exact appSpace_success (.blockOp blockop) args state value next mx safe peak run
  | globOp globop =>
    simp only [doApp] at run ⊢
    exact appSpace_success (.globOp globop) args state value next mx safe peak run
  | memOp memop =>
    simp only [doApp] at run ⊢
    exact appSpace_success (.memOp memop) args state value next mx safe peak run
  | thunkOp thunkop =>
    simp only [doApp] at run ⊢
    exact appSpace_success (.thunkOp thunkop) args state value next mx safe peak run

end Flapjack.Compiler.Backend.DataProps
