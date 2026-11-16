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
  obtain ⟨stackEq, localsSizeEq, _, _, localsEq, spaceEq,
    handlerEq, clockEq, frameSizesEq, compileEq⟩ :=
    doAppAux_fieldFrame op args state next value run
  simpa [Flapjack.SemanticPrimitivesProps.mapResult, stackEq, localsSizeEq, localsEq, spaceEq, handlerEq, clockEq, frameSizesEq, compileEq] using fields

/-- The successful space-and-auxiliary path preserves the returned value
under resource updates. This is proof infrastructure for the HOL swap. -/
private theorem appSpace_success {C F : Type} (op : ClosLang.Op)
    (args : List DataSem.Value) (state : State C F) (value : DataSem.Value) (next : State C F)
    (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : (match doSpace op args state with
      | none => Result.err (.abort .typeError)
      | some accounted =>
        doAppAux op args (doStack op args (doLimSafe accounted op args))) =
        .val (value, next)) :
    ∃ safe' peak' mx',
      (match doSpace op args { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak } with
      | none => Result.err (.abort .typeError)
      | some accounted => doAppAux op args (doStack op args (doLimSafe accounted op args))) =
        .val (value, { next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak' }) := by
  cases source : doSpace op args state with
  | none => simp [source] at run
  | some accounted =>
    have appRun : doAppAux op args (doStack op args (doLimSafe accounted op args)) =
        .val (value, next) := by
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


/-- Installation keeps the locals size and changes only the returned peak field
when locals-size, safety and peak observations change. -/
theorem doInstall_lssSafePeak {C F R : Type} (values : List DataSem.Value) (state : State C F)
    (lss : Option Nat) (safe : Bool) (peak : Nat) :
    doInstall (R := R) values { state with
                                localsSize := lss
                                safeForSpace := safe
                                peakHeapLength := peak } =
      match doInstall (R := R) values state with
      | .val (value, next) => .val (value, { next with localsSize := lss, peakHeapLength := peak })
      | .err error => .err error := by
  rcases values with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, rest⟩⟩⟩⟩⟩ <;> try rfl
  cases bytes : valueToBytes v1 <;> cases words : valueToWords v2 <;>
    simp [doInstall, bytes, words]
  all_goals repeat' (split <;> simp_all)

/-- Auxiliary success under locals-size, stack-maximum, safety and peak
updates. This Flapjack helper supports the HOL four-field swap. -/
private theorem doAppAux_lssStackSafePeakSwap {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (value : DataSem.Value) (next : State C F)
    (lss : Option Nat) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : doAppAux op values state = .val (value, next)) :
    ∃ safe' peak' lss' mx',
      doAppAux op values { state with
                           localsSize := lss
                           stackMax := mx
                           safeForSpace := safe
                           peakHeapLength := peak } =
        .val (value, { next with
                       localsSize := lss'
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) := by
  obtain ⟨safe', changed⟩ := doAppAux_safeSuccess op values state next value safe run
  have fields := doAppAux_withFields op values { state with safeForSpace := safe }
    state.stack lss mx peak state.locals state.space
    state.handler state.clock state.stackFrameSizes state.compile
  rw [changed] at fields
  refine ⟨safe', peak, lss, mx, ?_⟩
  obtain ⟨stackEq, localsSizeEq, _, _, localsEq, spaceEq,
    handlerEq, clockEq, frameSizesEq, compileEq⟩ :=
    doAppAux_fieldFrame op values state next value run
  simpa [Flapjack.SemanticPrimitivesProps.mapResult, stackEq, localsSizeEq, localsEq, spaceEq,
    handlerEq, clockEq, frameSizesEq, compileEq] using fields

/-- Stack and limit accounting respect locals-size, safety, peak and stack
maximum updates. This is proof infrastructure for the four-field swap. -/
private theorem doStack_doLimSafe_lssResource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat)
    (mx : Option Nat) (lss : Option Nat) :
    ∃ safe' peak' mx',
      doStack op values (doLimSafe { state with
                                     localsSize := lss
                                     safeForSpace := safe
                                     peakHeapLength := peak
                                     stackMax := mx } op values) =
        { doStack op values (doLimSafe state op values) with
          safeForSpace := safe', peakHeapLength := peak', stackMax := mx', localsSize := lss } := by
  let result := doStack op values (doLimSafe { state with
                                               localsSize := lss
                                               safeForSpace := safe
                                               peakHeapLength := peak
                                               stackMax := mx } op values)
  refine ⟨result.safeForSpace, result.peakHeapLength, result.stackMax, ?_⟩
  rfl

/-- The normal success path preserves the value under locals-size, stack,
safety and peak updates. This is proof infrastructure for the four-field swap. -/
private theorem appSpace_lssSuccess {C F : Type} (op : ClosLang.Op)
    (args : List DataSem.Value) (state : State C F) (value : DataSem.Value) (next : State C F)
    (lss : Option Nat) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : (match doSpace op args state with
      | none => Result.err (.abort .typeError)
      | some accounted =>
        doAppAux op args (doStack op args (doLimSafe accounted op args))) =
        .val (value, next)) :
    ∃ safe' peak' lss' mx',
      (match doSpace op args { state with
                               localsSize := lss
                               stackMax := mx
                               safeForSpace := safe
                               peakHeapLength := peak } with
      | none => Result.err (.abort .typeError)
      | some accounted => doAppAux op args (doStack op args (doLimSafe accounted op args))) =
        .val (value, { next with
                       localsSize := lss'
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) := by
  cases source : doSpace op args state with
  | none => simp [source] at run
  | some accounted =>
    have appRun : doAppAux op args (doStack op args (doLimSafe accounted op args)) =
        .val (value, next) := by
      simpa [source] using run
    obtain ⟨safe', peak', mx', target⟩ := doSpace_some_resource op args state accounted safe peak mx
      state.stack lss state.locals source
    have frame := doSpace_frame op args state accounted source
    have target' : doSpace op args { state with
                                     localsSize := lss
                                     stackMax := mx
                                     safeForSpace := safe
                                     peakHeapLength := peak } =
        some { accounted with
               localsSize := lss
               stackMax := mx'
               safeForSpace := safe'
               peakHeapLength := peak' } := by
      simpa only [frame.1, frame.2.1, frame.2.2.2.1] using target
    obtain ⟨safe'', peak'', mx'', account⟩ :=
      doStack_doLimSafe_lssResource op args accounted safe' peak' mx' lss
    obtain ⟨safe''', peak''', lss''', mx''', result⟩ := doAppAux_lssStackSafePeakSwap op args
      (doStack op args (doLimSafe accounted op args)) value next lss mx'' safe'' peak'' appRun
    exact ⟨safe''', peak''', lss''', mx''', by simpa only [target', account] using result⟩

/-- Exact HOL `do_app_lss_sm_safe_peak_swap`: primitive success is preserved
when locals size, stack maximum, safety and peak observations change. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_lss_sm_safe_peak_swap"]
theorem doApp_lssStackSafePeakSwap {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F)
    (lss : Option Nat) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : doApp op args state = .val (value, next)) :
    ∃ safe' peak' lss' mx',
      doApp op args { state with
                      localsSize := lss
                      stackMax := mx
                      safeForSpace := safe
                      peakHeapLength := peak } =
        .val (value, { next with
                       localsSize := lss'
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    have equation := doInstall_lssSafePeak (R := DataSem.Value) args
      { state with stackMax := none, stackFrameSizes := .ln } lss safe peak
    rw [run] at equation
    refine ⟨next.safeForSpace, peak, lss, next.stackMax, ?_⟩
    simpa using equation
  | intOp intop =>
    have normal := appSpace_lssSuccess (.intOp intop) args state value next lss mx safe peak
    cases intop <;> simp only [doApp] at run ⊢
    all_goals first | exact normal run | contradiction
  | label label =>
    simp only [doApp] at run ⊢
    exact appSpace_lssSuccess (.label label) args state value next lss mx safe peak run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact appSpace_lssSuccess (.ffi name) args state value next lss mx safe peak run
  | wordOp wordop =>
    simp only [doApp] at run ⊢
    exact appSpace_lssSuccess (.wordOp wordop) args state value next lss mx safe peak run
  | blockOp blockop =>
    simp only [doApp] at run ⊢
    exact appSpace_lssSuccess (.blockOp blockop) args state value next lss mx safe peak run
  | globOp globop =>
    simp only [doApp] at run ⊢
    exact appSpace_lssSuccess (.globOp globop) args state value next lss mx safe peak run
  | memOp memop =>
    simp only [doApp] at run ⊢
    exact appSpace_lssSuccess (.memOp memop) args state value next lss mx safe peak run
  | thunkOp thunkop =>
    simp only [doApp] at run ⊢
    exact appSpace_lssSuccess (.thunkOp thunkop) args state value next lss mx safe peak run

/-- Exact HOL `do_app_lss_sm_safe_peak_swap_aux`: the local auxiliary form of
the four-field resource swap. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_lss_sm_safe_peak_swap_aux"]
theorem doApp_lssStackSafePeakSwap_aux {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F)
    (lss : Option Nat) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : doApp op args state = .val (value, next)) :
    ∃ safe' peak' lss' mx',
      doApp op args { state with
                      localsSize := lss
                      stackMax := mx
                      safeForSpace := safe
                      peakHeapLength := peak } =
        .val (value, { next with
                       localsSize := lss'
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) :=
  doApp_lssStackSafePeakSwap op args state value next lss mx safe peak run

/-- Exact HOL `do_app_sm_safe_peak_swap_aux`: the local auxiliary form of the
three-field resource swap. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_sm_safe_peak_swap_aux"]
theorem doApp_stackSafePeakSwap_aux {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F) (mx : Option Nat) (safe : Bool)
    (peak : Nat) (run : doApp op args state = .val (value, next)) :
    ∃ safe' peak' mx', doApp op args { state with
                                       stackMax := mx
                                       safeForSpace := safe
                                       peakHeapLength := peak } =
      .val (value, { next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak' }) :=
  doApp_stackSafePeakSwap op args state value next mx safe peak run

/-- Exact HOL `do_app_aux_lss_sm_safe_peak_swap`: auxiliary primitive success
under locals-size, stack-maximum, safety and peak updates. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_lss_sm_safe_peak_swap"]
theorem doAppAux_lssStackSafePeakSwap_public {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (value : DataSem.Value) (next : State C F)
    (lss : Option Nat) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : doAppAux op values state = .val (value, next)) :
    ∃ safe' peak' lss' mx',
      doAppAux op values { state with
                           localsSize := lss
                           stackMax := mx
                           safeForSpace := safe
                           peakHeapLength := peak } =
        .val (value, { next with
                       localsSize := lss'
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) :=
  doAppAux_lssStackSafePeakSwap op values state value next lss mx safe peak run

/-- The space-and-auxiliary path preserves errors under locals-size, stack,
safety and peak updates. This assembles the four-field error case. -/
private theorem doApp_space_error_lssResource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat)
    (lss : Option Nat) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (run : (match doSpace op values state with
      | none => Flapjack.SemanticPrimitivesHOL.Result.err (.abort .typeError)
      | some next =>
        doAppAux op values (doStack op values (doLimSafe next op values))) =
        .err error) :
    (match doSpace op values { state with
                               localsSize := lss
                               safeForSpace := safe
                               peakHeapLength := peak
                               stackMax := mx } with
      | none => Flapjack.SemanticPrimitivesHOL.Result.err (.abort .typeError)
      | some next =>
        doAppAux op values (doStack op values (doLimSafe next op values))) =
        .err error := by
  cases source : doSpace op values state with
  | none =>
    have target := doSpace_none_resource op values state safe peak mx
      state.stack lss state.locals source
    simpa [source, target] using run
  | some next =>
    have appRun : doAppAux op values (doStack op values (doLimSafe next op values)) =
        .err error := by
      simpa [source] using run
    obtain ⟨safe', peak', mx', target⟩ := doSpace_some_resource op values state next safe peak mx
      state.stack lss state.locals source
    have frame := doSpace_frame op values state next source
    have target' : doSpace op values { state with
                                       localsSize := lss
                                       safeForSpace := safe
                                       peakHeapLength := peak
                                       stackMax := mx } =
        some { next with
               localsSize := lss
               safeForSpace := safe'
               peakHeapLength := peak'
               stackMax := mx' } := by
      simpa only [frame.1, frame.2.1, frame.2.2.2.1] using target
    obtain ⟨safe'', peak'', mx'', account⟩ :=
      doStack_doLimSafe_lssResource op values next safe' peak' mx' lss
    have result := doAppAux_error_resource op values (doStack op values (doLimSafe next op values))
      safe'' peak'' mx'' (doStack op values (doLimSafe next op values)).stack
      lss
      (doStack op values (doLimSafe next op values)).locals
      (doStack op values (doLimSafe next op values)).space error appRun
    simpa only [target', account] using result

/-- Primitive errors remain unchanged when locals size, stack maximum, safety
and peak observations change. -/
private theorem doApp_error_lssResource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat)
    (lss : Option Nat) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (run : doApp op values state = .err error) :
    doApp op values { state with
                      localsSize := lss
                      stackMax := mx
                      safeForSpace := safe
                      peakHeapLength := peak } = .err error := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    have equation := doInstall_lssSafePeak (R := DataSem.Value) values
      { state with stackMax := none, stackFrameSizes := .ln } lss safe peak
    rw [run] at equation
    simpa using equation
  | intOp intop =>
    have normal := doApp_space_error_lssResource (.intOp intop) values state safe peak mx lss error
    cases intop <;> simp only [doApp] at run ⊢
    all_goals first | exact normal run | exact run
  | label label =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssResource (.label label) values state safe peak mx lss error run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssResource (.ffi name) values state safe peak mx lss error run
  | wordOp wordop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssResource (.wordOp wordop) values state safe peak mx lss error run
  | blockOp blockop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssResource (.blockOp blockop) values state safe peak mx lss error run
  | globOp globop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssResource (.globOp globop) values state safe peak mx lss error run
  | memOp memop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssResource (.memOp memop) values state safe peak mx lss error run
  | thunkOp thunkop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssResource (.thunkOp thunkop) values state safe peak mx lss error run

/-- Exact HOL `do_app_err_lss_sm_safe_peak_swap`: primitive errors are unchanged
when locals size, stack maximum, safety and peak observations change. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_err_lss_sm_safe_peak_swap"]
theorem doApp_err_lssStackSafePeakSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (lss : Option Nat) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : doApp op values state = .err error) :
    doApp op values { state with
                      localsSize := lss
                      stackMax := mx
                      safeForSpace := safe
                      peakHeapLength := peak } = .err error :=
  doApp_error_lssResource op values state safe peak mx lss error run

/-- Failed space reservation is independent of a locals-size, stack and frame
sizes update. This Flapjack helper supports the HOL three-field swap. -/
theorem doSpace_none_lssStackFrameResource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (lss : Option Nat) (stk : List Stack)
    (stfrm : Spt Nat) (run : doSpace op values state = none) :
    doSpace op values { state with
                        localsSize := lss
                        stack := stk
                        stackFrameSizes := stfrm } = none := by
  cases reset : DataLang.opSpaceReset op
  · by_cases zero : DataSpace.opSpaceReq op values.length = 0
    · simp [doSpace, reset, zero] at run
    · by_cases low : state.space < DataSpace.opSpaceReq op values.length <;>
        simp_all [doSpace, consumeSpace]
  · simp [doSpace, reset] at run

/-- Successful space accounting preserves the swapped fields apart from the
safety and peak observations. This Flapjack helper supports the HOL three-field
swap. -/
theorem doSpace_some_lssStackFrameResource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state next : State C F) (lss : Option Nat)
    (stk : List Stack) (stfrm : Spt Nat) (run : doSpace op values state = some next) :
    ∃ safe' peak',
      doSpace op values { state with
                          localsSize := lss
                          stack := stk
                          stackFrameSizes := stfrm } =
        some { next with
               localsSize := lss
               stack := stk
               stackFrameSizes := stfrm
               safeForSpace := safe'
               peakHeapLength := peak' } := by
  classical
  let target := { state with
                  localsSize := lss
                  stack := stk
                  stackFrameSizes := stfrm }
  cases reset : DataLang.opSpaceReset op
  · by_cases zero : DataSpace.opSpaceReq op values.length = 0
    · simp [doSpace, reset, zero] at run
      subst next
      exact ⟨state.safeForSpace, state.peakHeapLength, by simp [doSpace, reset, zero]⟩
    · by_cases low : state.space < DataSpace.opSpaceReq op values.length
      · simp [doSpace, reset, zero, consumeSpace, low] at run
      · simp [doSpace, reset, zero, consumeSpace, low] at run
        subst next
        exact ⟨state.safeForSpace, state.peakHeapLength,
          by simp [doSpace, reset, zero, consumeSpace, low]⟩
  · simp [doSpace, reset] at run
    subst next
    refine ⟨target.safeForSpace && decide (noThunksInRefs target.refs ∧
      sizeOfHeapArgs values target + spaceConsumed target op values ≤ target.limits.heapLimit),
      max target.peakHeapLength (sizeOfHeapArgs values target + spaceConsumed target op values), ?_⟩
    simp [doSpace, reset, target]

/-- Stack and limit accounting respect a locals-size, stack and frame-sizes
update. This is proof infrastructure for the three-field swap. -/
private theorem doStack_doLimSafe_lssStackFrameResource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat)
    (mx : Option Nat) (lss : Option Nat) (stk : List Stack) (stfrm : Spt Nat) :
    ∃ safe' mx',
      doStack op values (doLimSafe { state with
                                     localsSize := lss
                                     safeForSpace := safe
                                     peakHeapLength := peak
                                     stackMax := mx
                                     stack := stk
                                     stackFrameSizes := stfrm } op values) =
        { doStack op values (doLimSafe state op values) with
          safeForSpace := safe'
          peakHeapLength := peak
          stackMax := mx'
          localsSize := lss
          stack := stk
          stackFrameSizes := stfrm } := by
  simp [doStack, doLimSafe]

/-- Installation keeps the locals size, stack and frame sizes while changing
only its own returned fields. This Flapjack helper supports the HOL three-field
swap. -/
theorem doInstall_lssStackFrame {C F R : Type} (values : List DataSem.Value) (state : State C F)
    (lss : Option Nat) (stk : List Stack) (stfrm : Spt Nat) :
    doInstall (R := R) values { state with
                                localsSize := lss
                                stack := stk
                                stackFrameSizes := stfrm } =
      match doInstall (R := R) values state with
      | .val (value, next) =>
        .val (value, { next with
                       localsSize := lss
                       stack := stk
                       stackFrameSizes := stfrm })
      | .err error => .err error := by
  rcases values with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, rest⟩⟩⟩⟩⟩ <;> try rfl
  cases bytes : valueToBytes v1 <;> cases words : valueToWords v2 <;>
    simp [doInstall, bytes, words]
  all_goals repeat' (split <;> simp_all)

/-- Auxiliary success under locals-size, stack, frame-sizes, stack-maximum and
safety updates. This Flapjack helper supports the HOL three-field swap. -/
private theorem doAppAux_lssStackFrameSwap {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (value : DataSem.Value) (next : State C F)
    (lss : Option Nat) (stk : List Stack) (stfrm : Spt Nat) (mx : Option Nat) (safe : Bool)
    (peak : Nat) (run : doAppAux op values state = .val (value, next)) :
    ∃ safe',
      doAppAux op values { state with
                           localsSize := lss
                           stack := stk
                           stackFrameSizes := stfrm
                           stackMax := mx
                           safeForSpace := safe
                           peakHeapLength := peak } =
        .val (value, { next with
                       localsSize := lss
                       stack := stk
                       stackFrameSizes := stfrm
                       stackMax := mx
                       safeForSpace := safe'
                       peakHeapLength := peak }) := by
  obtain ⟨safe', changed⟩ := doAppAux_safeSuccess op values state next value safe run
  have fields := doAppAux_withFields op values { state with safeForSpace := safe } stk lss mx
    peak state.locals state.space state.handler state.clock stfrm state.compile
  rw [changed] at fields
  refine ⟨safe', ?_⟩
  obtain ⟨stackEq, localsSizeEq, mxEq, peakEq, localsEq, spaceEq,
    handlerEq, clockEq, frameSizesEq, compileEq⟩ :=
    doAppAux_fieldFrame op values state next value run
  simpa [Flapjack.SemanticPrimitivesProps.mapResult, stackEq, localsSizeEq, mxEq, peakEq,
    localsEq, spaceEq, handlerEq, clockEq, frameSizesEq, compileEq] using fields

/-- Non-FFI primitive applications are independent of locals-size, stack,
frame-sizes, stack-maximum, safety and space updates on their failure path. -/
private theorem applyNonFfi_none_lssStackFrameResource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (lss : Option Nat) (stk : List Stack)
    (stfrm : Spt Nat) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (locals : Spt DataSem.Value) (space : Nat)
    (run : applyNonFfi op values state = none) :
    applyNonFfi op values { state with
                            localsSize := lss
                            stack := stk
                            stackFrameSizes := stfrm
                            stackMax := mx
                            safeForSpace := safe
                            peakHeapLength := peak
                            locals := locals
                            space := space } = none := by
  simp only [applyNonFfi] at run ⊢
  all_goals repeat' (split <;> simp_all [withFreshTimestamp])
  all_goals aesop

/-- Auxiliary errors under locals-size, stack, frame-sizes, stack-maximum,
safety and space updates. This Flapjack helper supports the HOL three-field
swap. -/
theorem doAppAux_error_lssStackFrameResource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (lss : Option Nat) (stk : List Stack)
    (stfrm : Spt Nat) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (locals : Spt DataSem.Value) (space : Nat)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (run : doAppAux op values state = .err error) :
    doAppAux op values { state with
                         localsSize := lss
                         stack := stk
                         stackFrameSizes := stfrm
                         stackMax := mx
                         safeForSpace := safe
                         peakHeapLength := peak
                         locals := locals
                         space := space } = .err error := by
  simp only [doAppAux] at run ⊢
  all_goals repeat' (split <;> simp_all)
  all_goals cases original : applyNonFfi op values state <;> simp_all
  all_goals
    have changed := applyNonFfi_none_lssStackFrameResource op values state lss stk stfrm mx safe
      peak locals space original
    simp_all

/-- The normal success path preserves the value under locals-size, stack and
frame-sizes updates. This is proof infrastructure for the three-field swap. -/
private theorem appSpace_lssStackFrameSuccess {C F : Type} (op : ClosLang.Op)
    (args : List DataSem.Value) (state : State C F) (value : DataSem.Value) (next : State C F)
    (lss : Option Nat) (stk : List Stack) (stfrm : Spt Nat)
    (run : (match doSpace op args state with
      | none => Result.err (.abort .typeError)
      | some accounted =>
        doAppAux op args (doStack op args (doLimSafe accounted op args))) =
        .val (value, next)) :
    ∃ safe' peak' mx',
      (match doSpace op args { state with
                               localsSize := lss
                               stack := stk
                               stackFrameSizes := stfrm } with
      | none => Result.err (.abort .typeError)
      | some accounted =>
        doAppAux op args (doStack op args (doLimSafe accounted op args))) =
        .val (value, { next with
                       localsSize := lss
                       stack := stk
                       stackFrameSizes := stfrm
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) := by
  cases source : doSpace op args state with
  | none => simp [source] at run
  | some accounted =>
    have appRun : doAppAux op args (doStack op args (doLimSafe accounted op args)) =
        .val (value, next) := by
      simpa [source] using run
    obtain ⟨safe', peak', target⟩ :=
      doSpace_some_lssStackFrameResource op args state accounted lss stk stfrm source
    obtain ⟨safe'', mx'', account⟩ :=
      doStack_doLimSafe_lssStackFrameResource op args accounted safe' peak' accounted.stackMax lss
      stk stfrm
    obtain ⟨safe''', result⟩ := doAppAux_lssStackFrameSwap op args
      (doStack op args (doLimSafe accounted op args)) value next lss stk stfrm mx'' safe'' peak'
      appRun
    exact ⟨safe''', peak', mx'', by simpa only [target, account] using result⟩

/-- Exact HOL `do_app_lss_stk_stfrm_swap` (`dataPropsScript.sml:608`): primitive
success is preserved when locals size, stack and frame sizes change. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_lss_stk_stfrm_swap"]
theorem doApp_lssStackFrameSwap {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F)
    (lss : Option Nat) (stk : List Stack) (stfrm : Spt Nat)
    (run : doApp op args state = .val (value, next)) :
    ∃ safe' peak' mx',
      doApp op args { state with
                      localsSize := lss
                      stack := stk
                      stackFrameSizes := stfrm } =
        .val (value, { next with
                       localsSize := lss
                       stack := stk
                       stackFrameSizes := match op with | .install => .ln | _ => stfrm
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    have equation := doInstall_lssStackFrame (R := DataSem.Value) args
      { state with stackMax := none, stackFrameSizes := .ln } lss stk .ln
    rw [run] at equation
    refine ⟨next.safeForSpace, next.peakHeapLength, next.stackMax, ?_⟩
    simpa using equation
  | intOp intop =>
    have normal := appSpace_lssStackFrameSuccess (.intOp intop) args state value next lss stk stfrm
    cases intop <;> simp only [doApp] at run ⊢
    all_goals first | exact normal run | contradiction
  | label label =>
    simp only [doApp] at run ⊢
    exact appSpace_lssStackFrameSuccess (.label label) args state value next lss stk stfrm run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact appSpace_lssStackFrameSuccess (.ffi name) args state value next lss stk stfrm run
  | wordOp wordop =>
    simp only [doApp] at run ⊢
    exact appSpace_lssStackFrameSuccess (.wordOp wordop) args state value next lss stk stfrm run
  | blockOp blockop =>
    simp only [doApp] at run ⊢
    exact appSpace_lssStackFrameSuccess (.blockOp blockop) args state value next lss stk stfrm run
  | globOp globop =>
    simp only [doApp] at run ⊢
    exact appSpace_lssStackFrameSuccess (.globOp globop) args state value next lss stk stfrm run
  | memOp memop =>
    simp only [doApp] at run ⊢
    exact appSpace_lssStackFrameSuccess (.memOp memop) args state value next lss stk stfrm run
  | thunkOp thunkop =>
    simp only [doApp] at run ⊢
    exact appSpace_lssStackFrameSuccess (.thunkOp thunkop) args state value next lss stk stfrm run

/-- Exact HOL `do_app_lss_stk_stfrm_swap_aux` (`dataPropsScript.sml:621`): the
local auxiliary form of the three-field swap, which HOL derives from the same
proof by `SIMP_RULE std_ss [LET_DEF]`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml"
  "do_app_lss_stk_stfrm_swap_aux"]
theorem doApp_lssStackFrameSwap_aux {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F)
    (lss : Option Nat) (stk : List Stack) (stfrm : Spt Nat)
    (run : doApp op args state = .val (value, next)) :
    ∃ safe' peak' mx',
      doApp op args { state with
                      localsSize := lss
                      stack := stk
                      stackFrameSizes := stfrm } =
        .val (value, { next with
                       localsSize := lss
                       stack := stk
                       stackFrameSizes := match op with | .install => .ln | _ => stfrm
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) :=
  doApp_lssStackFrameSwap op args state value next lss stk stfrm run

/-- The space-and-auxiliary path preserves errors under locals-size, stack and
frame-sizes updates. This assembles the three-field error case. -/
private theorem doApp_space_error_lssStackFrameResource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (lss : Option Nat) (stk : List Stack)
    (stfrm : Spt Nat) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (run : (match doSpace op values state with
      | none => Flapjack.SemanticPrimitivesHOL.Result.err (.abort .typeError)
      | some next =>
        doAppAux op values (doStack op values (doLimSafe next op values))) =
        .err error) :
    (match doSpace op values { state with
                               localsSize := lss
                               stack := stk
                               stackFrameSizes := stfrm } with
      | none => Flapjack.SemanticPrimitivesHOL.Result.err (.abort .typeError)
      | some next =>
        doAppAux op values (doStack op values (doLimSafe next op values))) =
        .err error := by
  cases source : doSpace op values state with
  | none =>
    have target := doSpace_none_lssStackFrameResource op values state lss stk stfrm source
    simpa [source, target] using run
  | some next =>
    have appRun : doAppAux op values (doStack op values (doLimSafe next op values)) =
        .err error := by
      simpa [source] using run
    obtain ⟨safe', peak', target⟩ :=
      doSpace_some_lssStackFrameResource op values state next lss stk stfrm source
    obtain ⟨safe'', mx'', account⟩ :=
      doStack_doLimSafe_lssStackFrameResource op values next safe' peak' next.stackMax lss stk
        stfrm
    have result := doAppAux_error_lssStackFrameResource op values
      (doStack op values (doLimSafe next op values)) lss stk stfrm mx'' safe'' peak'
      (doStack op values (doLimSafe next op values)).locals
      (doStack op values (doLimSafe next op values)).space error appRun
    simpa only [target, account] using result

/-- Primitive errors remain unchanged when locals size, stack and frame sizes
change. -/
private theorem doApp_error_lssStackFrameResource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (lss : Option Nat) (stk : List Stack)
    (stfrm : Spt Nat) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (run : doApp op values state = .err error) :
    doApp op values { state with
                      localsSize := lss
                      stack := stk
                      stackFrameSizes := stfrm } = .err error := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    have equation := doInstall_lssStackFrame (R := DataSem.Value) values
      { state with stackMax := none, stackFrameSizes := .ln } lss stk .ln
    rw [run] at equation
    simpa using equation
  | intOp intop =>
    have normal := doApp_space_error_lssStackFrameResource (.intOp intop) values state lss stk
      stfrm error
    cases intop <;> simp only [doApp] at run ⊢
    all_goals first | exact normal run | exact run
  | label label =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssStackFrameResource (.label label) values state lss stk stfrm
      error run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssStackFrameResource (.ffi name) values state lss stk stfrm error run
  | wordOp wordop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssStackFrameResource (.wordOp wordop) values state lss stk stfrm
      error run
  | blockOp blockop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssStackFrameResource (.blockOp blockop) values state lss stk stfrm
      error run
  | globOp globop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssStackFrameResource (.globOp globop) values state lss stk stfrm
      error run
  | memOp memop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssStackFrameResource (.memOp memop) values state lss stk stfrm
      error run
  | thunkOp thunkop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_lssStackFrameResource (.thunkOp thunkop) values state lss stk stfrm
      error run

/-- Exact HOL `do_app_err_lss_stk_stfrm_swap` (`dataPropsScript.sml:623`):
primitive errors are unchanged when locals size, stack and frame sizes change. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_err_lss_stk_stfrm_swap"]
theorem doApp_err_lssStackFrameSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (lss : Option Nat) (stk : List Stack) (stfrm : Spt Nat)
    (run : doApp op values state = .err error) :
    doApp op values { state with
                      localsSize := lss
                      stack := stk
                      stackFrameSizes := stfrm } = .err error :=
  doApp_error_lssStackFrameResource op values state lss stk stfrm error run

set_option maxHeartbeats 1000000 in
/-- The auxiliary dispatcher reads the configured limits only through its
length-safety test, so swapping them preserves the control flow and the returned
value and changes no field except the safety flag. This Flapjack helper supports
the HOL limit swap. -/
theorem applyNonFfi_limSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value) (lim : Limits) (safe : Bool) (peak : Nat)
    (mx : Option Nat)
    (run : applyNonFfi op values state = some (value, next)) :
    ∃ safe',
      applyNonFfi op values { state with
                              limits := lim
                              safeForSpace := safe
                              peakHeapLength := peak
                              stackMax := mx } =
        some (value, { next with
                       limits := lim
                       safeForSpace := safe'
                       peakHeapLength := peak
                       stackMax := mx }) := by
  simp only [applyNonFfi, Option.bind] at run ⊢
  all_goals
    repeat' (first | split at run | split)
  all_goals
    try simp_all [withFreshTimestamp, checkLim, Option.bind]
  all_goals try (aesop (config := {warnOnNonterminal := false}))
  all_goals cases safe <;> try simp_all
  all_goals omega

/-- Auxiliary success under a limits update. This Flapjack helper supports the
HOL limit swap. -/
private theorem doAppAux_limSwap {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value) (lim : Limits) (safe : Bool) (peak : Nat)
    (mx : Option Nat) (run : doAppAux op args state = .val (value, next)) :
    exists safe',
      doAppAux op args { state with
                         limits := lim
                         safeForSpace := safe
                         peakHeapLength := peak
                         stackMax := mx } =
        .val (value, { next with
                       limits := lim
                       safeForSpace := safe'
                       peakHeapLength := peak
                       stackMax := mx }) := by
  cases op with
  | ffi name =>
    simp only [doAppAux] at run ⊢
    rcases args with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;> try simp_all
    cases first <;> try simp_all
    case refPtr configBit configPtr =>
      cases second <;> try simp_all
      case refPtr dataBit dataPtr =>
        cases configLookup : sptLookup configPtr state.refs <;> try simp_all
        case some configEntry =>
          cases configEntry <;> try simp_all
          case byteArray configFlag config =>
            cases configFlag <;> try simp_all
            case true =>
              cases dataLookup : sptLookup dataPtr state.refs <;> try simp_all
              case some dataEntry =>
                cases dataEntry <;> try simp_all
                case byteArray dataFlag bytes =>
                  cases dataFlag <;> try simp_all
                  case false =>
                    cases call : callFFIHOL state.ffi (.extCall name) config bytes <;>
                      try simp_all
                    all_goals
                      obtain ⟨-, hnext⟩ := run
                      rw [← hnext]
                      simp
  | intOp intop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.intOp intop) args state with
    | none => simp_all
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      rw [original] at run
      injection run with hv
      injection hv with h1 h2
      obtain ⟨safe', changed⟩ :=
        applyNonFfi_limSwap (.intOp intop) args state next' value' lim safe peak mx original
      rw [h1, h2] at changed
      exact ⟨safe', by simp [changed]⟩
  | wordOp wordop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.wordOp wordop) args state with
    | none => simp_all
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      rw [original] at run
      injection run with hv
      injection hv with h1 h2
      obtain ⟨safe', changed⟩ :=
        applyNonFfi_limSwap (.wordOp wordop) args state next' value' lim safe peak mx original
      rw [h1, h2] at changed
      exact ⟨safe', by simp [changed]⟩
  | label label =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.label label) args state with
    | none => simp_all
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      rw [original] at run
      injection run with hv
      injection hv with h1 h2
      obtain ⟨safe', changed⟩ :=
        applyNonFfi_limSwap (.label label) args state next' value' lim safe peak mx original
      rw [h1, h2] at changed
      exact ⟨safe', by simp [changed]⟩
  | install =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.install) args state with
    | none => simp_all
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      rw [original] at run
      injection run with hv
      injection hv with h1 h2
      obtain ⟨safe', changed⟩ :=
        applyNonFfi_limSwap (.install) args state next' value' lim safe peak mx original
      rw [h1, h2] at changed
      exact ⟨safe', by simp [changed]⟩
  | thunkOp thunkop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.thunkOp thunkop) args state with
    | none => simp_all
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      rw [original] at run
      injection run with hv
      injection hv with h1 h2
      obtain ⟨safe', changed⟩ :=
        applyNonFfi_limSwap (.thunkOp thunkop) args state next' value' lim safe peak mx original
      rw [h1, h2] at changed
      exact ⟨safe', by simp [changed]⟩
  | globOp globop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.globOp globop) args state with
    | none => simp_all
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      rw [original] at run
      injection run with hv
      injection hv with h1 h2
      obtain ⟨safe', changed⟩ :=
        applyNonFfi_limSwap (.globOp globop) args state next' value' lim safe peak mx original
      rw [h1, h2] at changed
      exact ⟨safe', by simp [changed]⟩
  | blockOp blockop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.blockOp blockop) args state with
    | none => simp_all
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      rw [original] at run
      injection run with hv
      injection hv with h1 h2
      obtain ⟨safe', changed⟩ :=
        applyNonFfi_limSwap (.blockOp blockop) args state next' value' lim safe peak mx original
      rw [h1, h2] at changed
      exact ⟨safe', by simp [changed]⟩
  | memOp memop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.memOp memop) args state with
    | none => simp_all
    | some pair =>
      obtain ⟨value', next'⟩ := pair
      rw [original] at run
      injection run with hv
      injection hv with h1 h2
      obtain ⟨safe', changed⟩ :=
        applyNonFfi_limSwap (.memOp memop) args state next' value' lim safe peak mx original
      rw [h1, h2] at changed
      exact ⟨safe', by simp [changed]⟩

/-- Installation under a limits update. This Flapjack helper supports the HOL
limit swap. -/
theorem doInstall_limSwap {C F R : Type} (values : List DataSem.Value) (state : State C F)
    (lim : Limits) :
    doInstall (R := R) values { state with limits := lim } =
      match doInstall (R := R) values state with
      | .val (value, next) => .val (value, { next with limits := lim })
      | .err error => .err error := by
  rcases values with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, rest⟩⟩⟩⟩⟩ <;> try rfl
  cases bytes : valueToBytes v1 <;> cases words : valueToWords v2 <;>
    simp [doInstall, bytes, words]
  all_goals repeat' (split <;> simp_all)

/-- Failed space accounting is unchanged by a limits update. This Flapjack
helper supports the HOL limit swap. -/
theorem doSpace_none_limSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (lim : Limits) (run : doSpace op values state = none) :
    doSpace op values { state with limits := lim } = none := by
  cases reset : DataLang.opSpaceReset op
  · by_cases zero : DataSpace.opSpaceReq op values.length = 0
    · simp [doSpace, reset, zero] at run
    · by_cases low : state.space < DataSpace.opSpaceReq op values.length <;>
        simp_all [doSpace, consumeSpace]
  · simp [doSpace, reset] at run

/-- Successful space accounting under a limits update differs only in the
safety and peak observations. This Flapjack helper supports the HOL limit
swap. -/
theorem doSpace_some_limSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state next : State C F) (lim : Limits) (run : doSpace op values state = some next) :
    ∃ safe' peak',
      doSpace op values { state with limits := lim } =
        some { next with limits := lim, safeForSpace := safe', peakHeapLength := peak' } := by
  classical
  let target := { state with limits := lim }
  cases reset : DataLang.opSpaceReset op
  · by_cases zero : DataSpace.opSpaceReq op values.length = 0
    · simp [doSpace, reset, zero] at run
      subst next
      exact ⟨state.safeForSpace, state.peakHeapLength,
        by simp [doSpace, reset, zero]⟩
    · by_cases low : state.space < DataSpace.opSpaceReq op values.length
      · simp [doSpace, reset, zero, consumeSpace, low] at run
      · simp [doSpace, reset, zero, consumeSpace, low] at run
        subst next
        exact ⟨state.safeForSpace, state.peakHeapLength,
          by simp [doSpace, reset, zero, consumeSpace, low]⟩
  · simp [doSpace, reset] at run
    subst next
    refine ⟨target.safeForSpace && decide (noThunksInRefs target.refs ∧
      sizeOfHeapArgs values target + spaceConsumed target op values ≤ target.limits.heapLimit),
      max target.peakHeapLength (sizeOfHeapArgs values target + spaceConsumed target op values),
      ?_⟩
    simp [doSpace, reset, target]

/-- Stack and limit accounting respect a limits update. This Flapjack helper
supports the HOL limit swap. -/
private theorem doStack_doLimSafe_limSwap {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (lim : Limits) (safe : Bool)
    (peak : Nat) (mx : Option Nat) :
    ∃ safe' mx',
      doStack op values (doLimSafe { state with
                                     limits := lim
                                     safeForSpace := safe
                                     peakHeapLength := peak
                                     stackMax := mx } op values) =
        { doStack op values (doLimSafe state op values) with
          limits := lim
          safeForSpace := safe'
          peakHeapLength := peak
          stackMax := mx' } := by
  simp [doStack, doLimSafe]

/-- The normal success path preserves the value under a limits update. This is
proof infrastructure for the limit swap. -/
private theorem appSpace_limSuccess {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F) (lim : Limits)
    (run : (match doSpace op args state with
      | none => Result.err (.abort .typeError)
      | some accounted =>
        doAppAux op args (doStack op args (doLimSafe accounted op args))) =
        .val (value, next)) :
    ∃ safe' peak' mx',
      (match doSpace op args { state with limits := lim } with
      | none => Result.err (.abort .typeError)
      | some accounted =>
        doAppAux op args (doStack op args (doLimSafe accounted op args))) =
        .val (value, { next with
                       limits := lim
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) := by
  cases source : doSpace op args state with
  | none => simp [source] at run
  | some accounted =>
    have appRun : doAppAux op args (doStack op args (doLimSafe accounted op args)) =
        .val (value, next) := by
      simpa [source] using run
    obtain ⟨safe1, peak1, target⟩ := doSpace_some_limSwap op args state accounted lim source
    obtain ⟨safe2, mx2, account⟩ :=
      doStack_doLimSafe_limSwap op args accounted lim safe1 peak1 accounted.stackMax
    obtain ⟨safe3, result⟩ := doAppAux_limSwap op args
      (doStack op args (doLimSafe accounted op args)) next value lim safe2 peak1 mx2 appRun
    exact ⟨safe3, peak1, mx2, by simp [target, account, result]⟩

/-- Exact HOL `do_app_lim_swap_aux` (`dataPropsScript.sml:631`): primitive
success survives a limits update, with the safety, peak and stack-maximum
observations existential. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_lim_swap_aux"]
theorem doApp_limSwap_aux {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F) (lim : Limits)
    (run : doApp op args state = .val (value, next)) :
    ∃ safe' peak' mx',
      doApp op args { state with limits := lim } =
        .val (value, { next with
                       limits := lim
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    have equation := doInstall_limSwap (R := DataSem.Value) args
      { state with stackMax := none, stackFrameSizes := .ln } lim
    rw [run] at equation
    exact ⟨next.safeForSpace, next.peakHeapLength, next.stackMax, by simpa using equation⟩
  | intOp intop =>
    have normal := appSpace_limSuccess (.intOp intop) args state value next lim
    cases intop <;> simp only [doApp] at run ⊢
    all_goals first | exact normal run | contradiction
  | label label =>
    simp only [doApp] at run ⊢
    exact appSpace_limSuccess (.label label) args state value next lim run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact appSpace_limSuccess (.ffi name) args state value next lim run
  | wordOp wordop =>
    simp only [doApp] at run ⊢
    exact appSpace_limSuccess (.wordOp wordop) args state value next lim run
  | blockOp blockop =>
    simp only [doApp] at run ⊢
    exact appSpace_limSuccess (.blockOp blockop) args state value next lim run
  | globOp globop =>
    simp only [doApp] at run ⊢
    exact appSpace_limSuccess (.globOp globop) args state value next lim run
  | memOp memop =>
    simp only [doApp] at run ⊢
    exact appSpace_limSuccess (.memOp memop) args state value next lim run
  | thunkOp thunkop =>
    simp only [doApp] at run ⊢
    exact appSpace_limSuccess (.thunkOp thunkop) args state value next lim run

/-- Exact HOL `do_app_lim_swap` (`dataPropsScript.sml:633`), which HOL derives
from the auxiliary form by `SIMP_RULE std_ss [LET_DEF]`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_lim_swap"]
theorem doApp_limSwap {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F) (lim : Limits)
    (run : doApp op args state = .val (value, next)) :
    ∃ safe' peak' mx',
      doApp op args { state with limits := lim } =
        .val (value, { next with
                       limits := lim
                       stackMax := mx'
                       safeForSpace := safe'
                       peakHeapLength := peak' }) :=
  doApp_limSwap_aux op args state value next lim run

set_option maxHeartbeats 1000000 in
/-- Failed auxiliary applications are unchanged by a limits update, because the
dispatcher reads the configured limits only through its length-safety test. This
Flapjack helper supports the HOL limit swap; the heartbeat bump covers the
unfolded dispatcher case analysis. -/
theorem applyNonFfi_none_limSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (lim : Limits) (safe : Bool) (peak : Nat) (mx : Option Nat)
    (run : applyNonFfi op values state = none) :
    applyNonFfi op values { state with
                            limits := lim
                            safeForSpace := safe
                            peakHeapLength := peak
                            stackMax := mx } = none := by
  simp only [applyNonFfi, Option.bind] at run ⊢
  all_goals
    repeat' (first | split at run | split)
  all_goals
    try simp_all [withFreshTimestamp, checkLim, Option.bind]
  all_goals
    aesop

/-- Auxiliary errors are unchanged by a limits update. This Flapjack helper
supports the HOL limit swap. -/
private theorem doAppAux_err_limSwap {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (lim : Limits) (safe : Bool) (peak : Nat) (mx : Option Nat)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (run : doAppAux op args state = .err error) :
    doAppAux op args { state with
                       limits := lim
                       safeForSpace := safe
                       peakHeapLength := peak
                       stackMax := mx } = .err error := by
  cases op with
  | ffi name =>
    simp only [doAppAux] at run ⊢
    rcases args with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;> try simp_all
    cases first <;> try simp_all
    case refPtr configBit configPtr =>
      cases second <;> try simp_all
      case refPtr dataBit dataPtr =>
        cases configLookup : sptLookup configPtr state.refs <;> try simp_all
        case some configEntry =>
          cases configEntry <;> try simp_all
          case byteArray configFlag config =>
            cases configFlag <;> try simp_all
            case true =>
              cases dataLookup : sptLookup dataPtr state.refs <;> try simp_all
              case some dataEntry =>
                cases dataEntry <;> try simp_all
                case byteArray dataFlag bytes =>
                  cases dataFlag <;> try simp_all
                  case false =>
                    cases call : callFFIHOL state.ffi (.extCall name) config bytes <;>
                      try simp_all
  | intOp intop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.intOp intop) args state with
    | none =>
      have changed :=
        applyNonFfi_none_limSwap (.intOp intop) args state lim safe peak mx original
      simp_all
    | some pair => simp_all
  | wordOp wordop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.wordOp wordop) args state with
    | none =>
      have changed :=
        applyNonFfi_none_limSwap (.wordOp wordop) args state lim safe peak mx original
      simp_all
    | some pair => simp_all
  | label label =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.label label) args state with
    | none =>
      have changed :=
        applyNonFfi_none_limSwap (.label label) args state lim safe peak mx original
      simp_all
    | some pair => simp_all
  | install =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.install) args state with
    | none =>
      have changed :=
        applyNonFfi_none_limSwap (.install) args state lim safe peak mx original
      simp_all
    | some pair => simp_all
  | thunkOp thunkop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.thunkOp thunkop) args state with
    | none =>
      have changed :=
        applyNonFfi_none_limSwap (.thunkOp thunkop) args state lim safe peak mx original
      simp_all
    | some pair => simp_all
  | globOp globop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.globOp globop) args state with
    | none =>
      have changed :=
        applyNonFfi_none_limSwap (.globOp globop) args state lim safe peak mx original
      simp_all
    | some pair => simp_all
  | blockOp blockop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.blockOp blockop) args state with
    | none =>
      have changed :=
        applyNonFfi_none_limSwap (.blockOp blockop) args state lim safe peak mx original
      simp_all
    | some pair => simp_all
  | memOp memop =>
    simp only [doAppAux] at run ⊢
    cases original : applyNonFfi (.memOp memop) args state with
    | none =>
      have changed :=
        applyNonFfi_none_limSwap (.memOp memop) args state lim safe peak mx original
      simp_all
    | some pair => simp_all

/-- The space-and-auxiliary path preserves errors under a limits update. This
assembles the limit-swap error case. -/
private theorem appSpace_err_limResource {C F : Type} (op : ClosLang.Op)
    (args : List DataSem.Value) (state : State C F) (lim : Limits)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (run : (match doSpace op args state with
      | none => Flapjack.SemanticPrimitivesHOL.Result.err (.abort .typeError)
      | some accounted =>
        doAppAux op args (doStack op args (doLimSafe accounted op args))) = .err error) :
    (match doSpace op args { state with limits := lim } with
      | none => Flapjack.SemanticPrimitivesHOL.Result.err (.abort .typeError)
      | some accounted =>
        doAppAux op args (doStack op args (doLimSafe accounted op args))) = .err error := by
  cases source : doSpace op args state with
  | none =>
    have target := doSpace_none_limSwap op args state lim source
    simp_all
  | some accounted =>
    have appRun : doAppAux op args (doStack op args (doLimSafe accounted op args)) =
        .err error := by
      simpa [source] using run
    obtain ⟨safe1, peak1, target⟩ := doSpace_some_limSwap op args state accounted lim source
    obtain ⟨safe2, mx2, account⟩ :=
      doStack_doLimSafe_limSwap op args accounted lim safe1 peak1 accounted.stackMax
    have changed := doAppAux_err_limSwap op args
      (doStack op args (doLimSafe accounted op args)) lim safe2 peak1 mx2 error appRun
    simp [target, account, changed]

/-- Exact HOL `do_app_err_lim_swap` (`dataPropsScript.sml:637`): primitive
errors are unchanged by a limits update. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_err_lim_swap"]
theorem doApp_err_limSwap {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (lim : Limits) (run : doApp op args state = .err error) :
    doApp op args { state with limits := lim } = .err error := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    have equation := doInstall_limSwap (R := DataSem.Value) args
      { state with stackMax := none, stackFrameSizes := .ln } lim
    rw [run] at equation
    simpa using equation
  | intOp intop =>
    have normal := appSpace_err_limResource (.intOp intop) args state lim error
    cases intop <;> simp only [doApp] at run ⊢
    all_goals first | exact normal run | exact run
  | label label =>
    simp only [doApp] at run ⊢
    exact appSpace_err_limResource (.label label) args state lim error run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact appSpace_err_limResource (.ffi name) args state lim error run
  | wordOp wordop =>
    simp only [doApp] at run ⊢
    exact appSpace_err_limResource (.wordOp wordop) args state lim error run
  | blockOp blockop =>
    simp only [doApp] at run ⊢
    exact appSpace_err_limResource (.blockOp blockop) args state lim error run
  | globOp globop =>
    simp only [doApp] at run ⊢
    exact appSpace_err_limResource (.globOp globop) args state lim error run
  | memOp memop =>
    simp only [doApp] at run ⊢
    exact appSpace_err_limResource (.memOp memop) args state lim error run
  | thunkOp thunkop =>
    simp only [doApp] at run ⊢
    exact appSpace_err_limResource (.thunkOp thunkop) args state lim error run

end Flapjack.Compiler.Backend.DataProps
