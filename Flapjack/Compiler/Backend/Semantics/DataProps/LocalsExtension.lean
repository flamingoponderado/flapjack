import Flapjack.Compiler.Backend.DataSpace.Proofs.Sequence

/-! Preservation of non-type-error evaluation under local extension. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.Compiler.Backend.DataSpace Flapjack.SemanticPrimitivesHOL

/-- Same-program simulation when the target local environment extends the
source environment. This is Flapjack proof infrastructure. -/
def localsSimulationFor {C F : Type} (program : DataLang.Prog) : Prop :=
  ∀ (source sourceNext : State C F) (result : Option (Result (List Value) Value)) (locals : Spt Value),
    result ≠ some (.err (.abort .typeError)) → DataSem.evaluate program source = (result, sourceNext) →
    sptSubspt source.locals locals →
    ∃ out safe peak stackMax,
      DataSem.evaluate program { source with locals := locals } =
        (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      sptSubspt sourceNext.locals out

/-- A pass simulation is a same-program simulation when compilation leaves
the program unchanged. -/
theorem localsSimulation_of_unchanged {C F : Type} (program : DataLang.Prog)
    (same : compile program = program) (sim : simulationFor (C := C) (F := F) program) :
    localsSimulationFor (C := C) (F := F) program := by
  simpa [localsSimulationFor, simulationFor, same] using sim

/-- A pass simulation is also a same-program simulation when the compiled
and original programs evaluate identically. -/
theorem localsSimulation_of_evaluate_compile {C F : Type} (program : DataLang.Prog)
    (same : ∀ state : State C F, DataSem.evaluate (compile program) state = DataSem.evaluate program state)
    (sim : simulationFor (C := C) (F := F) program) : localsSimulationFor (C := C) (F := F) program := by
  intro source sourceNext result locals notType run included
  obtain ⟨out, safe, peak, stackMax, targetRun, final⟩ := sim source sourceNext result locals notType run included
  exact ⟨out, safe, peak, stackMax, by simpa [same] using targetRun, final⟩

/-- Local-extension simulations compose through sequences. -/
theorem localsSimulation_seq {C F : Type} (first second : DataLang.Prog)
    (firstIH : localsSimulationFor (C := C) (F := F) first)
    (secondIH : localsSimulationFor (C := C) (F := F) second) :
    localsSimulationFor (C := C) (F := F) (.seq first second) := by
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
      rw [DataSem.evaluate, fixClock_evaluate, targetFirst]
    | none =>
      obtain ⟨midLocals, midSafe, midPeak, midMax, targetFirst, midIncluded⟩ :=
        firstIH source mid none locals (by simp) firstRun included
      obtain ⟨out, safe, peak, stackMax, targetSecond, finalIncluded⟩ :=
        secondIH mid sourceNext result midLocals notType run midIncluded
      cases result with
      | none =>
        obtain ⟨safe', peak', stackMax', varied⟩ := evaluate_resource_variation_exact second
          { mid with locals := midLocals }
          { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          none midSafe midPeak midMax (by simp) targetSecond
        refine ⟨out, safe', peak', stackMax', ?_, finalIncluded⟩
        rw [DataSem.evaluate, fixClock_evaluate, targetFirst]
        simpa using varied
      | some stopped =>
        obtain ⟨safe', peak', stackMax', varied⟩ := evaluate_resource_variation_exact second
          { mid with locals := midLocals }
          { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          (some stopped) midSafe midPeak midMax notType targetSecond
        refine ⟨out, safe', peak', stackMax', ?_, finalIncluded⟩
        rw [DataSem.evaluate, fixClock_evaluate, targetFirst]
        simpa using varied

/-- Local-extension simulations compose through conditionals. -/
theorem localsSimulation_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (yesIH : localsSimulationFor (C := C) (F := F) yes)
    (noIH : localsSimulationFor (C := C) (F := F) no) :
    localsSimulationFor (C := C) (F := F) (.ifThenElse name yes no) := by
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
      exact ⟨out, safe, peak, stackMax, by simpa [DataSem.evaluate, targetRead, isTrue] using targetRun, final⟩
    · by_cases isFalse : DataSem.isBool false value
      · have branch : DataSem.evaluate no source = (result, sourceNext) := by
          simpa [DataSem.evaluate, read, isTrue, isFalse] using run
        obtain ⟨out, safe, peak, stackMax, targetRun, final⟩ := noIH source sourceNext result locals notType branch included
        exact ⟨out, safe, peak, stackMax, by simpa [DataSem.evaluate, targetRead, isTrue, isFalse] using targetRun, final⟩
      · simp [DataSem.evaluate, read, isTrue, isFalse] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)

/-- Every data program preserves non-type-error results when the local
environment is extended. This remains untagged pending source-carrier and
statement correspondence review. -/
theorem localsSimulation_all {C F : Type} (program : DataLang.Prog) : localsSimulationFor (C := C) (F := F) program := by
  have allSizes : ∀ weight : Nat, ∀ (program : DataLang.Prog), sizeOf program = weight →
      localsSimulationFor (C := C) (F := F) program := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
      intro program measure
      cases program with
      | skip =>
        apply localsSimulation_of_evaluate_compile .skip
        · intro state; simp [compile, space, pMakeSpace]
        · exact simulationFor_skip
      | move dest src =>
        apply localsSimulation_of_evaluate_compile (.move dest src)
        · intro state; simp [compile, space, pMakeSpace]
        · exact simulationFor_move dest src
      | assign dest op names live =>
        apply localsSimulation_of_evaluate_compile (.assign dest op names live)
        · intro state; simp [compile, space, pMakeSpace]
        · exact simulationFor_assign dest op names live
      | tick =>
        apply localsSimulation_of_evaluate_compile .tick
        · intro state; simp [compile, space, pMakeSpace]
        · exact simulationFor_tick
      | makeSpace amount names =>
        apply localsSimulation_of_evaluate_compile (.makeSpace amount names)
        · intro state; simp [compile, space, pMakeSpace, DataSem.evaluate_seq_skip]
        · exact simulationFor_makeSpace amount names
      | raise name =>
        apply localsSimulation_of_evaluate_compile (.raise name)
        · intro state; simp [compile, space, pMakeSpace]
        · exact simulationFor_raise name
      | «return» names =>
        apply localsSimulation_of_evaluate_compile (.return names)
        · intro state; simp [compile, space, pMakeSpace]
        · exact simulationFor_return names
      | seq first second =>
        apply localsSimulation_seq first second
        · apply ih (sizeOf first) ?_ first rfl
          simp only [DataLang.Prog.seq.sizeOf_spec] at measure
          omega
        · apply ih (sizeOf second) ?_ second rfl
          simp only [DataLang.Prog.seq.sizeOf_spec] at measure
          omega
      | ifThenElse name yes no =>
        apply localsSimulation_if name yes no
        · apply ih (sizeOf yes) ?_ yes rfl
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
          omega
        · apply ih (sizeOf no) ?_ no rfl
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
          omega
      | force ret label src =>
        apply localsSimulation_of_evaluate_compile (.force ret label src)
        · intro state; simp [compile, space, pMakeSpace]
        · exact simulationFor_force ret label src
      | call ret dest args handler =>
        apply localsSimulation_of_evaluate_compile (.call ret dest args handler)
        · intro state; simp [compile, space, pMakeSpace]
        · exact simulationFor_call ret dest args handler
  exact allSizes (sizeOf program) program rfl

/-- The evaluator's local-extension property in evaluation-pair form. -/
theorem evaluate_locals_extension {C F : Type} (program : DataLang.Prog)
    (source sourceNext : State C F) (result : Option (Result (List Value) Value)) (locals : Spt Value)
    (notType : result ≠ some (.err (.abort .typeError))) (run : DataSem.evaluate program source = (result, sourceNext))
    (included : sptSubspt source.locals locals) :
    ∃ out safe peak stackMax,
      DataSem.evaluate program { source with locals := locals } =
        (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      sptSubspt sourceNext.locals out := by
  exact localsSimulation_all program source sourceNext result locals notType run included

end Flapjack.Compiler.Backend.DataSem
