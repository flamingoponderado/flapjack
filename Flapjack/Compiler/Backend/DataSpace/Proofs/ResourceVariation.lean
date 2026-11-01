import Flapjack.Compiler.Backend.DataSpace.Proofs.Simulation
import Flapjack.Compiler.Backend.Semantics.DataProps.AbortControl
import Flapjack.Compiler.Backend.Semantics.DataProps.FrameResult
import Flapjack.Compiler.Backend.Semantics.DataProps.ValueFrameSize
import Flapjack.Compiler.Backend.Semantics.DataProps.AbortFrameSize

/-! Control-state consequences of resource-accounting variation. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Changing resource accounting preserves the result and every final field
except the accounting fields and `localsSize`. This Flapjack auxiliary lemma
is weaker than the HOL swap result, which also preserves `localsSize`. -/
theorem evaluate_resource_variation_control {C F : Type} (program : DataLang.Prog)
    (source sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (run : DataSem.evaluate program source = (result, sourceNext))
    (notType : result ≠ some (.err (.abort .typeError))) :
    ∃ localsSize safe' peak' stackMax',
      DataSem.evaluate program { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (result, { sourceNext with localsSize := localsSize, safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }) := by
  let target := { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
  obtain ⟨targetNext, targetRun, related, sameContinuingLocals⟩ :=
    evaluate_resource_variation program source sourceNext result safe peak stackMax run notType
  have localsAndStack : sourceNext.locals = targetNext.locals ∧ sourceNext.stack = targetNext.stack := by
    cases result with
    | none =>
      have sourceControl := evaluate_stackResult program source sourceNext none run
      have targetControl := evaluate_stackResult program target targetNext none targetRun
      exact ⟨sameContinuingLocals rfl, sourceControl.1.trans targetControl.1.symm⟩
    | some result =>
      cases result with
      | val values =>
        have sourceControl := evaluate_stackResult program source sourceNext (some (.val values)) run
        have targetControl := evaluate_stackResult program target targetNext (some (.val values)) targetRun
        exact ⟨(evaluate_value_locals program source sourceNext values run).trans
          (evaluate_value_locals program target targetNext values targetRun).symm,
          sourceControl.1.trans targetControl.1.symm⟩
      | err error =>
        cases error with
        | abort reason =>
          have notTypeReason : reason ≠ .typeError := by simpa using notType
          have sourceControl := evaluate_abort_control program source sourceNext reason notTypeReason run
          have targetControl := evaluate_abort_control program target targetNext reason notTypeReason targetRun
          exact ⟨sourceControl.1.trans targetControl.1.symm, sourceControl.2.trans targetControl.2.symm⟩
        | raise value =>
          obtain ⟨jumped, jumpRun, sourceStack, _, sourceLocals⟩ :=
            evaluate_stackResult program source sourceNext (some (.err (.raise value))) run
          obtain ⟨targetJump, targetJumpRun, targetStack, _, targetLocals⟩ :=
            evaluate_stackResult program target targetNext (some (.err (.raise value))) targetRun
          have moved := jumpExc_transport source target jumped rfl rfl jumpRun
          have jumpEq := Option.some.inj (targetJumpRun.symm.trans moved)
          subst targetJump
          exact ⟨sourceLocals.trans targetLocals.symm, sourceStack.trans targetStack.symm⟩
  have stateEq : targetNext = { sourceNext with localsSize := targetNext.localsSize, safeForSpace := targetNext.safeForSpace, peakHeapLength := targetNext.peakHeapLength, stackMax := targetNext.stackMax } := by
    rcases related with ⟨code, clock, space, ffi, refs, global, handler, _, compiler, oracle, stamps, limits, frames, _⟩
    obtain ⟨locals, stack⟩ := localsAndStack
    cases sourceNext
    cases targetNext
    simp_all
  exact ⟨targetNext.localsSize, targetNext.safeForSpace, targetNext.peakHeapLength,
    targetNext.stackMax, by simpa [target, ← stateEq] using targetRun⟩

/-- The full resource-field swap holds for continuing executions. -/
theorem evaluate_resource_variation_normal {C F : Type} (program : DataLang.Prog)
    (source sourceNext : State C F) (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (run : DataSem.evaluate program source = (none, sourceNext)) :
    ∃ safe' peak' stackMax',
      DataSem.evaluate program { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (none, { sourceNext with safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }) := by
  obtain ⟨localsSize, safe', peak', stackMax', targetRun⟩ :=
    evaluate_resource_variation_control program source sourceNext none safe peak stackMax run (by simp)
  have originalSize := evaluate_frameSizeResult program source sourceNext none run
  have targetSize := evaluate_frameSizeResult program
    { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
    { sourceNext with localsSize := localsSize, safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }
    none targetRun
  have sizeEq : localsSize = sourceNext.localsSize := by
    change localsSize = source.localsSize at targetSize
    exact targetSize.trans originalSize.symm
  subst localsSize
  exact ⟨safe', peak', stackMax', by simpa using targetRun⟩

/-- The full resource-field swap also holds when evaluation raises. -/
theorem evaluate_resource_variation_raise {C F : Type} (program : DataLang.Prog)
    (source sourceNext : State C F) (value : DataSem.Value) (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (run : DataSem.evaluate program source = (some (.err (.raise value)), sourceNext)) :
    ∃ safe' peak' stackMax',
      DataSem.evaluate program { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (some (.err (.raise value)), { sourceNext with safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }) := by
  obtain ⟨localsSize, safe', peak', stackMax', targetRun⟩ :=
    evaluate_resource_variation_control program source sourceNext (some (.err (.raise value))) safe peak stackMax run (by simp)
  obtain ⟨jumped, jumpRun, originalSize⟩ :=
    evaluate_frameSizeResult program source sourceNext (some (.err (.raise value))) run
  obtain ⟨targetJump, targetJumpRun, targetSize⟩ := evaluate_frameSizeResult program
    { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
    { sourceNext with localsSize := localsSize, safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }
    (some (.err (.raise value))) targetRun
  have moved := jumpExc_transport source
    { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } jumped rfl rfl jumpRun
  have jumpEq := Option.some.inj (targetJumpRun.symm.trans moved)
  subst targetJump
  have sizeEq : localsSize = sourceNext.localsSize := by
    change localsSize = jumped.localsSize at targetSize
    exact targetSize.trans originalSize.symm
  subst localsSize
  exact ⟨safe', peak', stackMax', by simpa using targetRun⟩

/-- The exact resource-field swap for returned values. -/
theorem evaluate_resource_variation_value {C F : Type} (program : DataLang.Prog)
    (source sourceNext : State C F) (values : List DataSem.Value) (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (run : DataSem.evaluate program source = (some (.val values), sourceNext)) :
    ∃ safe' peak' stackMax',
      DataSem.evaluate program { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (some (.val values), { sourceNext with safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }) := by
  obtain ⟨localsSize, safe', peak', stackMax', targetRun⟩ :=
    evaluate_resource_variation_control program source sourceNext (some (.val values)) safe peak stackMax run (by simp)
  have originalSize := evaluate_value_localsSize program source sourceNext values run
  have targetSize := evaluate_value_localsSize program
    { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
    { sourceNext with localsSize := localsSize, safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }
    values targetRun
  have sizeEq : localsSize = sourceNext.localsSize := targetSize.trans originalSize.symm
  subst localsSize
  exact ⟨safe', peak', stackMax', by simpa using targetRun⟩

/-- The exact resource-field swap for FFI aborts. Timeout needs separate
reasoning because some timeout paths retain their current frame size. -/
theorem evaluate_resource_variation_ffiAbort {C F : Type} (program : DataLang.Prog)
    (source sourceNext : State C F) (event : HolFinalEvent) (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (run : DataSem.evaluate program source = (some (.err (.abort (.ffiError event))), sourceNext)) :
    ∃ safe' peak' stackMax',
      DataSem.evaluate program { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (some (.err (.abort (.ffiError event))), { sourceNext with safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }) := by
  obtain ⟨localsSize, safe', peak', stackMax', targetRun⟩ :=
    evaluate_resource_variation_control program source sourceNext (some (.err (.abort (.ffiError event)))) safe peak stackMax run (by simp)
  have originalSize := (evaluate_abort_frameSize program source sourceNext (.ffiError event) (by simp) (by simp) run).1
  have targetSize := (evaluate_abort_frameSize program
    { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
    { sourceNext with localsSize := localsSize, safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }
    (.ffiError event) (by simp) (by simp) targetRun).1
  have sizeEq : localsSize = sourceNext.localsSize := targetSize.trans originalSize.symm
  subst localsSize
  exact ⟨safe', peak', stackMax', by simpa using targetRun⟩

/-- Exact resource variation for every outcome except a type error or
timeout. -/
theorem evaluate_resource_variation_nonTimeout {C F : Type} (program : DataLang.Prog)
    (source sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (run : DataSem.evaluate program source = (result, sourceNext))
    (notType : result ≠ some (.err (.abort .typeError)))
    (notTimeout : result ≠ some (.err (.abort .timeoutError))) :
    ∃ safe' peak' stackMax',
      DataSem.evaluate program { source with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (result, { sourceNext with safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }) := by
  cases result with
  | none => exact evaluate_resource_variation_normal program source sourceNext safe peak stackMax run
  | some result =>
    cases result with
    | val values => exact evaluate_resource_variation_value program source sourceNext values safe peak stackMax run
    | err error =>
      cases error with
      | raise value => exact evaluate_resource_variation_raise program source sourceNext value safe peak stackMax run
      | abort reason =>
        cases reason with
        | typeError => exact False.elim (notType rfl)
        | timeoutError => exact False.elim (notTimeout rfl)
        | ffiError event => exact evaluate_resource_variation_ffiAbort program source sourceNext event safe peak stackMax run

end Flapjack.Compiler.Backend.DataSpace
