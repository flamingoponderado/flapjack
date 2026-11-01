import Flapjack.Compiler.Backend.DataSpace.Proofs.SequenceAssign

/-! Assembly of the data-space reservation simulation. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Every data program satisfies the local-extension simulation for the
reservation pass. This theorem remains untagged pending source evaluator and
state-carrier correspondence review. -/
theorem simulationFor_all {C F : Type} (program : DataLang.Prog) : simulationFor (C := C) (F := F) program := by
  have allSizes : ∀ weight : Nat, ∀ (program : DataLang.Prog), sizeOf program = weight →
      simulationFor (C := C) (F := F) program := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
      intro program measure
      cases program with
      | skip => exact simulationFor_skip
      | move dest src => exact simulationFor_move dest src
      | assign dest op args names => exact simulationFor_assign dest op args names
      | tick => exact simulationFor_tick
      | makeSpace amount names => exact simulationFor_makeSpace amount names
      | raise name => exact simulationFor_raise name
      | «return» names => exact simulationFor_return names
      | force ret label src => exact simulationFor_force ret label src
      | call ret dest args handler => exact simulationFor_call ret dest args handler
      | ifThenElse name yes no =>
        apply simulationFor_if name yes no
        · apply ih (sizeOf yes) ?_ yes rfl
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
          omega
        · apply ih (sizeOf no) ?_ no rfl
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
          omega
      | seq first second =>
        have firstIH : simulationFor (C := C) (F := F) first := by
          apply ih (sizeOf first) ?_ first rfl
          simp only [DataLang.Prog.seq.sizeOf_spec] at measure
          omega
        have secondIH : simulationFor (C := C) (F := F) second := by
          apply ih (sizeOf second) ?_ second rfl
          simp only [DataLang.Prog.seq.sizeOf_spec] at measure
          omega
        cases first with
        | skip => exact simulationFor_seq_skip_left second secondIH
        | move dest src => exact simulationFor_seq_move_left dest src second secondIH
        | makeSpace amount names => exact simulationFor_seq_makeSpace_left amount names second secondIH
        | assign dest op args names =>
          cases names with
          | none => exact simulationFor_seq_assign_left dest op args second secondIH
          | some names =>
            apply simulationFor_seq_nonHoistable (.assign dest op args (some names)) second firstIH secondIH <;> simp
        | call ret dest args handler =>
          apply simulationFor_seq_nonHoistable (.call ret dest args handler) second firstIH secondIH <;> simp
        | seq a b =>
          apply simulationFor_seq_nonHoistable (.seq a b) second firstIH secondIH <;> simp
        | ifThenElse name yes no =>
          apply simulationFor_seq_nonHoistable (.ifThenElse name yes no) second firstIH secondIH <;> simp
        | raise name =>
          apply simulationFor_seq_nonHoistable (.raise name) second firstIH secondIH <;> simp
        | «return» names =>
          apply simulationFor_seq_nonHoistable (.return names) second firstIH secondIH <;> simp
        | tick =>
          apply simulationFor_seq_nonHoistable .tick second firstIH secondIH <;> simp
        | force ret label src =>
          apply simulationFor_seq_nonHoistable (.force ret label src) second firstIH secondIH <;> simp
  exact allSizes (sizeOf program) program rfl

/-- A stopped non-type-error evaluation is preserved by the reservation
pass up to resource-accounting fields. This remains untagged pending review
of the evaluator and carrier against HOL. -/
theorem compile_correct_stopped {C F : Type} (program : DataLang.Prog) (source sourceNext : State C F)
    (result : Result (List DataSem.Value) DataSem.Value)
    (run : DataSem.evaluate program source = (some result, sourceNext))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ safe peak stackMax,
      DataSem.evaluate (compile program) source =
        (some result, { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) := by
  have included : sptSubspt source.locals source.locals := by
    intro key member
    exact ⟨member, rfl⟩
  obtain ⟨_, safe, peak, stackMax, targetRun, _⟩ :=
    simulationFor_all program source sourceNext (some result) source.locals (by simpa using notType) run included
  exact ⟨safe, peak, stackMax, by simpa using targetRun⟩

/-- Reservation-pass correctness in evaluation-pair form. The stopped and
non-type-error premises and three resource fields follow the source result;
this remains untagged until the evaluator and carriers are source-reviewed. -/
theorem compile_correct {C F : Type} (program : DataLang.Prog) (source : State C F)
    (notType : (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)))
    (stopped : (DataSem.evaluate program source).1 ≠ none) :
    ∃ safe peak stackMax,
      DataSem.evaluate (compile program) source =
        ((DataSem.evaluate program source).1,
          { (DataSem.evaluate program source).2 with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) := by
  cases run : DataSem.evaluate program source with
  | mk outcome sourceNext =>
    cases outcome with
    | none => simp [run] at stopped
    | some result =>
      have noType : result ≠ .err (.abort .typeError) := by simpa [run] using notType
      obtain ⟨safe, peak, stackMax, correct⟩ := compile_correct_stopped program source sourceNext result run noType
      exact ⟨safe, peak, stackMax, by simpa only [run] using correct⟩

end Flapjack.Compiler.Backend.DataSpace
