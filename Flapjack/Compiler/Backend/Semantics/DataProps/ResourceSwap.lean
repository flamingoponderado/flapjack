module

public import Flapjack.Compiler.Backend.Semantics.DataProps.NonFfiResources
public import Flapjack.Compiler.Backend.Semantics.DataProps.HeapSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyAuxFields

@[expose] public section

/-! Primitive success under resource-field updates. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Safety updates preserve successful auxiliary applications, including FFI.
This Flapjack helper supports the HOL resource-swap proof. -/
private theorem doAppAux_safeSuccess {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value) (safe : Bool)
    (run : doAppAux op values state = .val (value, next)) :
    ∃ safe', doAppAux op values {state with safeForSpace := safe} =
      .val (value, {next with safeForSpace := safe'}) := by
  simp only [doAppAux] at run ⊢
  all_goals repeat' (split at run <;> simp_all)
  all_goals try (obtain ⟨safe', result⟩ := (applyNonFfi_successFields _ _ state next value safe (by assumption)).1; simp_all)
  all_goals try aesop

/-- Auxiliary primitive success is preserved by updating resource fields. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_sm_safe_peak_swap"]
theorem doAppAux_stackSafePeakSwap {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : doAppAux op args state = .val (value, next)) :
    ∃ safe' peak' mx', doAppAux op args {state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak} =
      .val (value, {next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak'}) := by
  obtain ⟨safe', changed⟩ := doAppAux_safeSuccess op args state next value safe run
  have fields := doAppAux_withFields op args {state with safeForSpace := safe}
    state.stack state.localsSize mx peak state.locals state.space
    state.handler state.clock state.stackFrameSizes state.compile
  rw [changed] at fields
  refine ⟨safe', peak, mx, ?_⟩
  obtain ⟨stackEq, localsSizeEq, _, _, localsEq, spaceEq, handlerEq, clockEq, frameSizesEq, compileEq⟩ :=
    doAppAux_fieldFrame op args state next value run
  simpa [Flapjack.SemanticPrimitivesProps.mapResult, stackEq, localsSizeEq, localsEq, spaceEq, handlerEq, clockEq, frameSizesEq, compileEq] using fields

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
    obtain ⟨safe', peak', mx', target⟩ := doSpace_some_resource op args state accounted safe peak mx state.stack state.localsSize state.locals source
    have frame := doSpace_frame op args state accounted source
    have target' : doSpace op args { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak } =
        some { accounted with stackMax := mx', safeForSpace := safe', peakHeapLength := peak' } := by
      simpa only [frame.1, frame.2.1, frame.2.2.2.1] using target
    obtain ⟨safe'', peak'', mx'', account⟩ := doStack_doLimSafe_resource op args accounted safe' peak' mx'
    obtain ⟨safe''', peak''', mx''', result⟩ := doAppAux_stackSafePeakSwap op args
      (doStack op args (doLimSafe accounted op args)) value next mx'' safe'' peak'' appRun
    exact ⟨safe''', peak''', mx''', by simpa only [target', account] using result⟩

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

/-- Auxiliary primitive success is preserved by safety and peak updates. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_safe_peak_swap"]
theorem doAppAux_safePeakSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F) (safe : Bool) (peak : Nat)
    (run : doAppAux op values state = .val (value, next)) :
    ∃ safe' peak', doAppAux op values {state with safeForSpace := safe, peakHeapLength := peak} =
      .val (value, {next with safeForSpace := safe', peakHeapLength := peak'}) := by
  obtain ⟨safe', peak', mx', result⟩ := doAppAux_stackSafePeakSwap op values state value next state.stackMax safe peak run
  have first := (doAppAux_fieldFrame op values state next value run).2.2.1
  have second := doAppAux_fieldFrame op values {state with stackMax := state.stackMax, safeForSpace := safe, peakHeapLength := peak}
    {next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak'} value result
  have same : mx' = next.stackMax := second.2.2.1.trans first.symm
  have peakEq : peak' = peak := second.2.2.2.1
  subst mx'
  subst peak'
  exact ⟨safe', peak, by simpa using result⟩


/-- Space accounting preserves the stack maximum. This is proof infrastructure. -/
private theorem spaceStack {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state next : State C F) (run : doSpace op values state = some next) : next.stackMax = state.stackMax := by
  cases reset : DataLang.opSpaceReset op
  · by_cases zero : DataSpace.opSpaceReq op values.length = 0
    · simp [doSpace, reset, zero] at run
      subst next
      rfl
    · by_cases low : state.space < DataSpace.opSpaceReq op values.length
      · simp [doSpace, reset, zero, consumeSpace, low] at run
      · simp [doSpace, reset, zero, consumeSpace, low] at run
        subst next
        rfl
  · simp [doSpace, reset] at run
    subst next
    rfl

/-- Successful space accounting respects safety and peak updates. This is proof infrastructure. -/
private theorem spaceSafe {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state next : State C F) (safe : Bool) (peak : Nat) (run : doSpace op values state = some next) :
    ∃ safe' peak', doSpace op values {state with safeForSpace := safe, peakHeapLength := peak} =
      some {next with safeForSpace := safe', peakHeapLength := peak'} := by
  obtain ⟨safe', peak', mx', result⟩ := doSpace_some_resource op values state next safe peak state.stackMax state.stack state.localsSize state.locals run
  have frame := doSpace_frame op values state next run
  have result' : doSpace op values { state with safeForSpace := safe, peakHeapLength := peak } =
      some { next with safeForSpace := safe', peakHeapLength := peak', stackMax := mx' } := by
    simpa only [frame.1, frame.2.1, frame.2.2.2.1] using result
  have first := spaceStack op values state next run
  have second := spaceStack op values {state with safeForSpace := safe, peakHeapLength := peak, stackMax := state.stackMax}
    {next with safeForSpace := safe', peakHeapLength := peak', stackMax := mx'} result'
  have same : mx' = next.stackMax := second.trans first.symm
  subst mx'
  exact ⟨safe', peak', by simpa using result'⟩

/-- Limit and stack accounting respect safety and peak updates. This is proof infrastructure. -/
private theorem stackSafe {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (safe : Bool) (peak : Nat) :
    ∃ safe', doStack op values (doLimSafe {state with safeForSpace := safe, peakHeapLength := peak} op values) =
      {doStack op values (doLimSafe state op values) with safeForSpace := safe', peakHeapLength := peak} := by
  let result := doStack op values (doLimSafe {state with safeForSpace := safe, peakHeapLength := peak} op values)
  exact ⟨result.safeForSpace, rfl⟩

/-- The normal primitive success path respects safety and peak updates. This is proof infrastructure. -/
private theorem appSpaceSafe {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F) (safe : Bool) (peak : Nat)
    (run : (match doSpace op values state with
      | none => Result.err (.abort .typeError)
      | some accounted => doAppAux op values (doStack op values (doLimSafe accounted op values))) = .val (value,next)) :
    ∃ safe' peak', (match doSpace op values {state with safeForSpace := safe, peakHeapLength := peak} with
      | none => Result.err (.abort .typeError)
      | some accounted => doAppAux op values (doStack op values (doLimSafe accounted op values))) =
        .val (value,{next with safeForSpace := safe', peakHeapLength := peak'}) := by
  cases source : doSpace op values state with
  | none => simp [source] at run
  | some accounted =>
    have appRun : doAppAux op values (doStack op values (doLimSafe accounted op values)) = .val (value,next) := by
      simpa [source] using run
    obtain ⟨safe', peak', target⟩ := spaceSafe op values state accounted safe peak source
    obtain ⟨safe'', account⟩ := stackSafe op values accounted safe' peak'
    obtain ⟨safe''', peak''', result⟩ := doAppAux_safePeakSwap op values
      (doStack op values (doLimSafe accounted op values)) value next safe'' peak' appRun
    exact ⟨safe''', peak''', by simpa only [target, account] using result⟩

/-- Primitive success is preserved by safety and peak updates. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_safe_peak_swap"]
theorem doApp_safePeakSwap {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F) (safe : Bool) (peak : Nat)
    (run : doApp op args state = .val (value, next)) :
    ∃ safe' peak', doApp op args { state with safeForSpace := safe, peakHeapLength := peak } =
      .val (value, { next with safeForSpace := safe', peakHeapLength := peak' }) := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    have equation := doInstall_safePeak (R := DataSem.Value) args
      { state with stackMax := none, stackFrameSizes := .ln } safe peak
    rw [run] at equation
    refine ⟨next.safeForSpace, peak, ?_⟩
    simpa using equation
  | intOp intop =>
    have normal := appSpaceSafe (.intOp intop) args state value next safe peak
    cases intop <;> simp only [doApp] at run ⊢
    all_goals first | exact normal run | contradiction
  | label label =>
    simp only [doApp] at run ⊢
    exact appSpaceSafe (.label label) args state value next safe peak run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact appSpaceSafe (.ffi name) args state value next safe peak run
  | wordOp wordop =>
    simp only [doApp] at run ⊢
    exact appSpaceSafe (.wordOp wordop) args state value next safe peak run
  | blockOp blockop =>
    simp only [doApp] at run ⊢
    exact appSpaceSafe (.blockOp blockop) args state value next safe peak run
  | globOp globop =>
    simp only [doApp] at run ⊢
    exact appSpaceSafe (.globOp globop) args state value next safe peak run
  | memOp memop =>
    simp only [doApp] at run ⊢
    exact appSpaceSafe (.memOp memop) args state value next safe peak run
  | thunkOp thunkop =>
    simp only [doApp] at run ⊢
    exact appSpaceSafe (.thunkOp thunkop) args state value next safe peak run

end Flapjack.Compiler.Backend.DataProps
