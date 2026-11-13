module

public import Flapjack.Compiler.Backend.DataSpace.Proofs.Simulation
public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateResourceSwap

@[expose] public section

/-! Evaluation is stable when locals are extended. -/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

private def LocalSimulation {C F : Type} (program : DataLang.Prog) : Prop :=
  ∀ (source sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value)) (locals : Spt DataSem.Value),
    result ≠ some (.err (.abort .typeError)) → DataSem.evaluate program source = (result, sourceNext) →
    sptSubspt source.locals locals →
    ∃ out safe peak stackMax,
      DataSem.evaluate program { source with locals := locals } =
        (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      sptSubspt sourceNext.locals out

private theorem localSimulation_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (yesIH : LocalSimulation (C := C) (F := F) yes)
    (noIH : LocalSimulation (C := C) (F := F) no) :
    LocalSimulation (C := C) (F := F) (.ifThenElse name yes no) := by
  intro source sourceNext result locals notType run included
  cases read : DataSem.getVar name source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some value =>
    have targetRead : DataSem.getVar name locals = some value := (sptSubsptLookup _ _).1 included name value read
    by_cases isTrue : DataSem.isBool true value
    · have branch : DataSem.evaluate yes source = (result, sourceNext) := by
        simpa [DataSem.evaluate, read, isTrue] using run
      obtain ⟨out, safe, peak, stackMax, targetRun, final⟩ := yesIH source sourceNext result locals notType branch included
      refine ⟨out, safe, peak, stackMax, ?_, final⟩
      simpa [DataSem.evaluate, targetRead, isTrue] using targetRun
    · by_cases isFalse : DataSem.isBool false value
      · have branch : DataSem.evaluate no source = (result, sourceNext) := by
          simpa [DataSem.evaluate, read, isTrue, isFalse] using run
        obtain ⟨out, safe, peak, stackMax, targetRun, final⟩ := noIH source sourceNext result locals notType branch included
        refine ⟨out, safe, peak, stackMax, ?_, final⟩
        simpa [DataSem.evaluate, targetRead, isTrue, isFalse] using targetRun
      · simp [DataSem.evaluate, read, isTrue, isFalse] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)

private theorem localSimulation_seq {C F : Type} (first second : DataLang.Prog)
    (firstIH : LocalSimulation (C := C) (F := F) first)
    (secondIH : LocalSimulation (C := C) (F := F) second) :
    LocalSimulation (C := C) (F := F) (.seq first second) := by
  intro source sourceNext result locals notType run included
  rw [DataSem.evaluate, fixClock_evaluate] at run
  cases firstRun : DataSem.evaluate first source with
  | mk firstResult sourceMid =>
    rw [firstRun] at run
    cases firstResult with
    | none =>
      obtain ⟨midLocals, safe1, peak1, stack1, targetFirst, midIncluded⟩ :=
        firstIH source sourceMid none locals (by simp) firstRun included
      simp only [if_true] at targetFirst
      obtain ⟨out, safe2, peak2, stack2, targetSecond, finalIncluded⟩ :=
        secondIH sourceMid sourceNext result midLocals notType run midIncluded
      obtain ⟨stack3, safe3, peak3, transported⟩ :=
        evaluate_stackSafePeakSwap stack1 safe1
          (if result = none then { sourceNext with locals := out, safeForSpace := safe2, peakHeapLength := peak2, stackMax := stack2 }
            else { sourceNext with safeForSpace := safe2, peakHeapLength := peak2, stackMax := stack2 })
          { sourceMid with locals := midLocals } result peak1 second targetSecond
      refine ⟨out, safe3, peak3, stack3, ?_, finalIncluded⟩
      rw [DataSem.evaluate, fixClock_evaluate, targetFirst]
      cases result <;> simpa using transported
    | some outcome =>
      have eqs : result = some outcome ∧ sourceNext = sourceMid := Prod.mk.inj run.symm
      obtain ⟨rfl, rfl⟩ := eqs
      obtain ⟨out, safe, peak, stackMax, targetFirst, finalIncluded⟩ :=
        firstIH source sourceNext (some outcome) locals notType firstRun included
      refine ⟨out, safe, peak, stackMax, ?_, finalIncluded⟩
      rw [DataSem.evaluate, fixClock_evaluate, targetFirst]

private theorem localSimulation_all {C F : Type} (program : DataLang.Prog) :
    LocalSimulation (C := C) (F := F) program := by
  have allSizes : ∀ weight : Nat, ∀ program : DataLang.Prog,
      sizeOf program = weight → LocalSimulation (C := C) (F := F) program := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
      intro program measure
      cases program with
      | skip =>
        simpa [LocalSimulation, DataSpace.simulationFor, DataSpace.compile, DataSpace.space, DataSpace.pMakeSpace] using
          (DataSpace.simulationFor_skip (C := C) (F := F))
      | move dest src =>
        simpa [LocalSimulation, DataSpace.simulationFor, DataSpace.compile, DataSpace.space, DataSpace.pMakeSpace] using
          (DataSpace.simulationFor_move (C := C) (F := F) dest src)
      | assign dest op args names =>
        simpa [LocalSimulation, DataSpace.simulationFor, DataSpace.compile, DataSpace.space, DataSpace.pMakeSpace] using
          (DataSpace.simulationFor_assign (C := C) (F := F) dest op args names)
      | tick =>
        simpa [LocalSimulation, DataSpace.simulationFor, DataSpace.compile, DataSpace.space, DataSpace.pMakeSpace] using
          (DataSpace.simulationFor_tick (C := C) (F := F))
      | makeSpace amount names =>
        simpa [LocalSimulation, DataSpace.simulationFor, DataSpace.compile, DataSpace.space,
          DataSpace.pMakeSpace, DataSem.evaluate_seq_skip] using
          (DataSpace.simulationFor_makeSpace (C := C) (F := F) amount names)
      | raise name =>
        simpa [LocalSimulation, DataSpace.simulationFor, DataSpace.compile, DataSpace.space, DataSpace.pMakeSpace] using
          (DataSpace.simulationFor_raise (C := C) (F := F) name)
      | «return» names =>
        simpa [LocalSimulation, DataSpace.simulationFor, DataSpace.compile, DataSpace.space, DataSpace.pMakeSpace] using
          (DataSpace.simulationFor_return (C := C) (F := F) names)
      | seq first second =>
        apply localSimulation_seq first second
        · apply ih (sizeOf first) ?_ first rfl
          simp only [DataLang.Prog.seq.sizeOf_spec] at measure
          omega
        · apply ih (sizeOf second) ?_ second rfl
          simp only [DataLang.Prog.seq.sizeOf_spec] at measure
          omega
      | ifThenElse name yes no =>
        apply localSimulation_if name yes no
        · apply ih (sizeOf yes) ?_ yes rfl
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
          omega
        · apply ih (sizeOf no) ?_ no rfl
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
          omega
      | force ret label src =>
        simpa [LocalSimulation, DataSpace.simulationFor, DataSpace.compile, DataSpace.space, DataSpace.pMakeSpace] using
          (DataSpace.simulationFor_force (C := C) (F := F) ret label src)
      | call ret dest args handler =>
        simpa [LocalSimulation, DataSpace.simulationFor, DataSpace.compile, DataSpace.space, DataSpace.pMakeSpace] using
          (DataSpace.simulationFor_call (C := C) (F := F) ret dest args handler)

  exact allSizes (sizeOf program) program rfl

/-- Enlarging the source locals preserves any non-type-error evaluation,
with only the original resource fields allowed to change. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_locals"]
theorem evaluate_locals {C F V : Type} (program : DataLang.Prog) (source : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value)) (sourceNext : State C F)
    (_vars : V) (locals : Spt DataSem.Value)
    (notType : result ≠ some (.err (.abort .typeError)))
    (run : DataSem.evaluate program source = (result, sourceNext))
    (included : localsOk source.locals locals) :
    ∃ out safe peak stackMax,
      DataSem.evaluate program { source with locals := locals } =
        (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, stackMax := stackMax, peakHeapLength := peak }
          else { sourceNext with safeForSpace := safe, stackMax := stackMax, peakHeapLength := peak }) ∧
      localsOk sourceNext.locals out := by
  exact localSimulation_all program source sourceNext result locals notType run included

end Flapjack.Compiler.Backend.DataProps
