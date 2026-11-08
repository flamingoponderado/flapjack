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

end Flapjack.Compiler.Backend.DataSem
