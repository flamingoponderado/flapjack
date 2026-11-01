import Flapjack.Compiler.Backend.DataSpace.Proofs.ResourceVariation

/-! Composition of reservation simulations through sequences. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- When the second component leaves no deferred reservation, the pass
retains a sequence except for its skip and reservation special cases. -/
theorem compile_seq_plain_of_noReservation (first second body : DataLang.Prog)
    (found : space second = .inl body) (notSkip : first ≠ .skip)
    (notSpace : ∀ amount names, first ≠ .makeSpace amount names) :
    compile (.seq first second) = .seq (compile first) (compile second) := by
  cases first <;> simp_all [compile, space, pMakeSpace]

/-- A deferred reservation also stays in the second component when the
first instruction is not one of the hoistable forms. -/
theorem compile_seq_plain_of_nonHoistable (first second : DataLang.Prog) (amount : Nat)
    (names : NumSet) (body : DataLang.Prog) (found : space second = .inr (amount, names, body))
    (notSkip : first ≠ .skip) (notSpace : ∀ amount names, first ≠ .makeSpace amount names)
    (notMove : ∀ dest src, first ≠ .move dest src)
    (notAssign : ∀ dest op args, first ≠ .assign dest op args none) :
    compile (.seq first second) = .seq (compile first) (compile second) := by
  cases first <;> simp_all [compile, space, pMakeSpace]

/-- The continuing case of sequence simulation when the reservation pass
retains both compiled components in order. This auxiliary case is untagged. -/
theorem simulationFor_seq_plain_normal {C F : Type} (first second : DataLang.Prog)
    (firstIH : simulationFor (C := C) (F := F) first)
    (secondIH : simulationFor (C := C) (F := F) second)
    (shape : compile (.seq first second) = .seq (compile first) (compile second))
    (source sourceNext : State C F) (locals : Spt DataSem.Value)
    (run : DataSem.evaluate (.seq first second) source = (none, sourceNext))
    (included : sptSubspt source.locals locals) :
    ∃ out safe peak stackMax,
      DataSem.evaluate (compile (.seq first second)) { source with locals := locals } =
        (none, { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      sptSubspt sourceNext.locals out := by
  rw [DataSem.evaluate, fixClock_evaluate] at run
  cases firstRun : DataSem.evaluate first source with
  | mk outcome mid =>
    rw [firstRun] at run
    cases outcome with
    | some stopped => simp at run
    | none =>
      obtain ⟨midLocals, midSafe, midPeak, midMax, targetFirst, midIncluded⟩ :=
        firstIH source mid none locals (by simp) firstRun included
      obtain ⟨out, safe, peak, stackMax, targetSecond, finalIncluded⟩ :=
        secondIH mid sourceNext none midLocals (by simp) run midIncluded
      obtain ⟨safe', peak', stackMax', varied⟩ :=
        evaluate_resource_variation_normal (compile second) { mid with locals := midLocals }
          { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          midSafe midPeak midMax targetSecond
      refine ⟨out, safe', peak', stackMax', ?_, finalIncluded⟩
      rw [shape, DataSem.evaluate, fixClock_evaluate, targetFirst]
      simpa using varied

/-- The raised-result case of a sequence whose compiled form retains both
components in order. -/
theorem simulationFor_seq_plain_raise {C F : Type} (first second : DataLang.Prog)
    (firstIH : simulationFor (C := C) (F := F) first)
    (secondIH : simulationFor (C := C) (F := F) second)
    (shape : compile (.seq first second) = .seq (compile first) (compile second))
    (source sourceNext : State C F) (locals : Spt DataSem.Value) (value : DataSem.Value)
    (run : DataSem.evaluate (.seq first second) source = (some (.err (.raise value)), sourceNext))
    (included : sptSubspt source.locals locals) :
    ∃ out safe peak stackMax,
      DataSem.evaluate (compile (.seq first second)) { source with locals := locals } =
        (some (.err (.raise value)), { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      sptSubspt sourceNext.locals out := by
  rw [DataSem.evaluate, fixClock_evaluate] at run
  cases firstRun : DataSem.evaluate first source with
  | mk outcome mid =>
    rw [firstRun] at run
    cases outcome with
    | some stopped =>
      simp only [Prod.mk.injEq, Option.some.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨out, safe, peak, stackMax, targetFirst, finalIncluded⟩ :=
        firstIH source mid (some (.err (.raise value))) locals (by simp) firstRun included
      refine ⟨out, safe, peak, stackMax, ?_, finalIncluded⟩
      rw [shape, DataSem.evaluate, fixClock_evaluate, targetFirst]
      rfl
    | none =>
      obtain ⟨midLocals, midSafe, midPeak, midMax, targetFirst, midIncluded⟩ :=
        firstIH source mid none locals (by simp) firstRun included
      obtain ⟨out, safe, peak, stackMax, targetSecond, finalIncluded⟩ :=
        secondIH mid sourceNext (some (.err (.raise value))) midLocals (by simp) run midIncluded
      obtain ⟨safe', peak', stackMax', varied⟩ :=
        evaluate_resource_variation_raise (compile second) { mid with locals := midLocals }
          { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          value midSafe midPeak midMax targetSecond
      refine ⟨out, safe', peak', stackMax', ?_, finalIncluded⟩
      rw [shape, DataSem.evaluate, fixClock_evaluate, targetFirst]
      simpa using varied

/-- Sequencing combines two simulations when the compiled second component
admits the exact resource-field swap for all non-type-error outcomes. The
swap premise is still open for timeouts. -/
theorem simulationFor_seq_plain_of_resourceSwap {C F : Type} (first second : DataLang.Prog)
    (firstIH : simulationFor (C := C) (F := F) first)
    (secondIH : simulationFor (C := C) (F := F) second)
    (shape : compile (.seq first second) = .seq (compile first) (compile second))
    (resourceSwap : ∀ (state next : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
      (safe : Bool) (peak : Nat) (stackMax : Option Nat),
      result ≠ some (.err (.abort .typeError)) →
      DataSem.evaluate (compile second) state = (result, next) →
      ∃ safe' peak' stackMax',
        DataSem.evaluate (compile second) { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
          (result, { next with safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' })) :
    simulationFor (C := C) (F := F) (.seq first second) := by
  intro source sourceNext result locals notType run included
  rw [DataSem.evaluate, fixClock_evaluate] at run
  cases firstRun : DataSem.evaluate first source with
  | mk outcome mid =>
    rw [firstRun] at run
    cases outcome with
    | some stopped =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨out, safe, peak, stackMax, targetFirst, finalIncluded⟩ :=
        firstIH source mid (some stopped) locals notType firstRun included
      refine ⟨out, safe, peak, stackMax, ?_, finalIncluded⟩
      rw [shape, DataSem.evaluate, fixClock_evaluate, targetFirst]
    | none =>
      obtain ⟨midLocals, midSafe, midPeak, midMax, targetFirst, midIncluded⟩ :=
        firstIH source mid none locals (by simp) firstRun included
      obtain ⟨out, safe, peak, stackMax, targetSecond, finalIncluded⟩ :=
        secondIH mid sourceNext result midLocals notType run midIncluded
      cases result with
      | none =>
        obtain ⟨safe', peak', stackMax', varied⟩ := resourceSwap { mid with locals := midLocals }
          { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          none midSafe midPeak midMax (by simp) targetSecond
        refine ⟨out, safe', peak', stackMax', ?_, finalIncluded⟩
        rw [shape, DataSem.evaluate, fixClock_evaluate, targetFirst]
        simpa using varied
      | some stopped =>
        obtain ⟨safe', peak', stackMax', varied⟩ := resourceSwap { mid with locals := midLocals }
          { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          (some stopped) midSafe midPeak midMax notType targetSecond
        refine ⟨out, safe', peak', stackMax', ?_, finalIncluded⟩
        rw [shape, DataSem.evaluate, fixClock_evaluate, targetFirst]
        simpa using varied

/-- Retained sequence composition holds for every non-type-error result
except timeout, whose exact resource swap remains open. -/
theorem simulationFor_seq_plain_nonTimeout {C F : Type} (first second : DataLang.Prog)
    (firstIH : simulationFor (C := C) (F := F) first)
    (secondIH : simulationFor (C := C) (F := F) second)
    (shape : compile (.seq first second) = .seq (compile first) (compile second))
    (source sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (locals : Spt DataSem.Value) (notType : result ≠ some (.err (.abort .typeError)))
    (notTimeout : result ≠ some (.err (.abort .timeoutError)))
    (run : DataSem.evaluate (.seq first second) source = (result, sourceNext))
    (included : sptSubspt source.locals locals) :
    ∃ out safe peak stackMax,
      DataSem.evaluate (compile (.seq first second)) { source with locals := locals } =
        (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      sptSubspt sourceNext.locals out := by
  rw [DataSem.evaluate, fixClock_evaluate] at run
  cases firstRun : DataSem.evaluate first source with
  | mk outcome mid =>
    rw [firstRun] at run
    cases outcome with
    | some stopped =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨out, safe, peak, stackMax, targetFirst, finalIncluded⟩ :=
        firstIH source mid (some stopped) locals notType firstRun included
      refine ⟨out, safe, peak, stackMax, ?_, finalIncluded⟩
      rw [shape, DataSem.evaluate, fixClock_evaluate, targetFirst]
    | none =>
      obtain ⟨midLocals, midSafe, midPeak, midMax, targetFirst, midIncluded⟩ :=
        firstIH source mid none locals (by simp) firstRun included
      obtain ⟨out, safe, peak, stackMax, targetSecond, finalIncluded⟩ :=
        secondIH mid sourceNext result midLocals notType run midIncluded
      cases result with
      | none =>
        obtain ⟨safe', peak', stackMax', varied⟩ := evaluate_resource_variation_nonTimeout (compile second)
          { mid with locals := midLocals }
          { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          none midSafe midPeak midMax targetSecond (by simp) (by simp)
        refine ⟨out, safe', peak', stackMax', ?_, finalIncluded⟩
        rw [shape, DataSem.evaluate, fixClock_evaluate, targetFirst]
        simpa using varied
      | some stopped =>
        obtain ⟨safe', peak', stackMax', varied⟩ := evaluate_resource_variation_nonTimeout (compile second)
          { mid with locals := midLocals }
          { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          (some stopped) midSafe midPeak midMax targetSecond notType notTimeout
        refine ⟨out, safe', peak', stackMax', ?_, finalIncluded⟩
        rw [shape, DataSem.evaluate, fixClock_evaluate, targetFirst]
        simpa using varied
end Flapjack.Compiler.Backend.DataSpace
