module

public import Flapjack.Compiler.Backend.DataLive.Proofs.EvaluatorCall
public import Flapjack.Misc.ClockWeightInduction

@[expose] public section

/-! Clock and program-size induction for same-program evaluator simulation. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Same-program simulation for all data programs on related states. This is
auxiliary infrastructure; it is not tagged as the HOL stack-swap theorem. -/
theorem evaluatorSimulation_all {C F : Type} (program : DataLang.Prog) :
    evaluatorSimulation (C := C) (F := F) program := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := fun program source => ∀ target sourceNext result, stateRel source target .ln →
      source.locals = target.locals → exceptionRel source target →
      result ≠ some (.err (.abort .typeError)) →
      DataSem.evaluate program source = (result, sourceNext) →
      ∃ targetNext, DataSem.evaluate program target = (result, targetNext) ∧
        stateRel sourceNext targetNext .ln ∧
          (result = none → sourceNext.locals = targetNext.locals)) ?_ program
  intro program source exprIH₀ smaller₀
  have exprIH := fun (program' : DataLang.Prog) (src target sourceNext : State C F)
      (result : Option (Result (List DataSem.Value) DataSem.Value)) h1 h2 related sameLocals
      exception notType run =>
    exprIH₀ program' src h1 h2 target sourceNext result related sameLocals exception notType run
  have smaller := fun (program' : DataLang.Prog) (src target sourceNext : State C F)
      (result : Option (Result (List DataSem.Value) DataSem.Value)) h1 related sameLocals
      exception notType run =>
    smaller₀ program' src h1 target sourceNext result related sameLocals exception notType run
  intro target sourceNext result related sameLocals exception notType run
  have below : evaluatorSimulationBelow (C := C) (F := F) source.clock := by
    intro program source target sourceNext result smaller related sameLocals exception notType run
    exact smaller₀ program source smaller target sourceNext result related sameLocals
      exception notType run
  cases program with
  | skip => exact evaluatorSimulation_skip source target sourceNext result related sameLocals
              exception notType run
  | move dest src => exact evaluatorSimulation_move dest src source target sourceNext result related
                       sameLocals exception notType run
  | assign dest op names live => exact evaluatorSimulation_assign dest op names live source target
                                   sourceNext result related sameLocals exception notType run
  | tick => exact evaluatorSimulation_tick source target sourceNext result related sameLocals
              exception notType run
  | makeSpace amount names => exact evaluatorSimulation_makeSpace amount names source target
                                sourceNext result related sameLocals exception notType run
  | raise name => exact evaluatorSimulation_raise name source target sourceNext result related
                    sameLocals exception notType run
  | «return» names => exact evaluatorSimulation_return names source target sourceNext result related
                        sameLocals exception notType run
  | force ret label src =>
    exact evaluatorSimulation_force_at ret label src source target sourceNext result related
      sameLocals exception notType run below
  | call ret dest names handler =>
    exact evaluatorSimulation_call_at ret dest names handler source target sourceNext result
      related sameLocals exception notType run below
  | seq first second =>
    have firstSize : sizeOf first < sizeOf (first.seq second) := by
      simp only [DataLang.Prog.seq.sizeOf_spec] at ⊢
      omega
    have secondSize : sizeOf second < sizeOf (first.seq second) := by
      simp only [DataLang.Prog.seq.sizeOf_spec] at ⊢
      omega
    rw [DataSem.evaluate, fixClock_evaluate] at run
    cases firstRun : DataSem.evaluate first source with
    | mk firstResult sourceMid =>
      rw [firstRun] at run
      cases firstResult with
      | none =>
        obtain ⟨targetMid, targetFirst, midRel, midLocals⟩ :=
          exprIH first source target sourceMid none (by omega) firstSize related sameLocals
            exception (by simp) firstRun
        have sourceControl := evaluate_stackResult first source sourceMid none firstRun
        have targetControl := evaluate_stackResult first target targetMid none targetFirst
        have midException := exceptionRel_after source target sourceMid targetMid .ln midRel
          exception
          sourceControl.1 sourceControl.2 targetControl.1 targetControl.2
        have midClock : sourceMid.clock ≤ source.clock := by
          have bound := evaluate_clock_le first source
          rw [firstRun] at bound
          change sourceMid.clock ≤ source.clock at bound
          omega
        obtain ⟨targetNext, targetSecond, finalRel, finalLocals⟩ :=
          exprIH second sourceMid targetMid sourceNext result midClock secondSize midRel
            (midLocals rfl) midException notType run
        refine ⟨targetNext, ?_, finalRel, finalLocals⟩
        rw [DataSem.evaluate, fixClock_evaluate, targetFirst]
        exact targetSecond
      | some outcome =>
        have equal : result = some outcome ∧ sourceNext = sourceMid := Prod.mk.inj run.symm
        obtain ⟨rfl, rfl⟩ := equal
        obtain ⟨targetNext, targetFirst, finalRel, _⟩ :=
          exprIH first source target sourceNext (some outcome) (by omega) firstSize related
            sameLocals exception notType firstRun
        refine ⟨targetNext, ?_, finalRel, by simp⟩
        rw [DataSem.evaluate, fixClock_evaluate, targetFirst]
  | ifThenElse name yes no =>
    have yesSize : sizeOf yes < sizeOf (DataLang.Prog.ifThenElse name yes no) := by
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at ⊢
      omega
    have noSize : sizeOf no < sizeOf (DataLang.Prog.ifThenElse name yes no) := by
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at ⊢
      omega
    have readEq : DataSem.getVar name source.locals = DataSem.getVar name target.locals := by rw
      [sameLocals]
    cases read : DataSem.getVar name source.locals with
    | none =>
      simp [DataSem.evaluate, read] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some value =>
      have targetRead : DataSem.getVar name target.locals = some value := by rw [← readEq, read]
      by_cases isTrue : DataSem.isBool true value
      · have branch : DataSem.evaluate yes source = (result, sourceNext) := by simpa
          [DataSem.evaluate, read, isTrue] using run
        obtain ⟨targetNext, targetRun, finalRel, locals⟩ :=
          exprIH yes source target sourceNext result (by omega) yesSize related sameLocals exception
            notType branch
        exact ⟨targetNext, by simpa [DataSem.evaluate, targetRead, isTrue] using targetRun,
          finalRel, locals⟩
      · by_cases isFalse : DataSem.isBool false value
        · have branch : DataSem.evaluate no source = (result, sourceNext) := by simpa
            [DataSem.evaluate, read, isTrue, isFalse] using run
          obtain ⟨targetNext, targetRun, finalRel, locals⟩ :=
            exprIH no source target sourceNext result (by omega) noSize related sameLocals exception
              notType branch
          exact ⟨targetNext, by simpa [DataSem.evaluate, targetRead, isTrue, isFalse] using
            targetRun, finalRel, locals⟩
        · simp [DataSem.evaluate, read, isTrue, isFalse] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notType rfl)

end Flapjack.Compiler.Backend.DataLive
