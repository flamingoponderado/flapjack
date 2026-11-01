import Flapjack.Compiler.Backend.BviToData.Optimise
import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
import Flapjack.Compiler.Backend.DataLive.Proofs.CompileCorrect
import Flapjack.Compiler.Backend.DataSimp.Proofs.Correct
import Flapjack.Compiler.Backend.DataSpace.Proofs.CompileCorrect

/-! Composition of the established data optimization steps. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Liveness followed by sequence simplification preserves a stopped,
non-type-error result and changes only the four state fields permitted by
the source optimization theorem. This intermediate composition has no
separate HOL declaration. -/
theorem live_simp_correct {C F : Type} (program : DataLang.Prog) (state : State C F)
    (notType : (DataSem.evaluate program state).1 ≠ some (.err (.abort .typeError)))
    (stopped : (DataSem.evaluate program state).1 ≠ none) :
    ∃ localsSize stackMax safe peak,
      DataSem.evaluate (DataSimp.simp (DataLive.compile program .ln).1 .skip) state =
        ((DataSem.evaluate program state).1,
          { (DataSem.evaluate program state).2 with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) := by
  obtain ⟨localsSize, stackMax, safe, peak, correct⟩ := DataLive.compile_correct program state notType stopped
  exact ⟨localsSize, stackMax, safe, peak, by simpa only [DataSimp.simp_correct] using correct⟩

/-- The complete liveness, simplification and space-reservation sequence
preserves stopped non-type-error results. This theorem remains untagged until
the evaluator and state carriers are reviewed against HOL. -/
theorem optimise_correct {C F : Type} (program : DataLang.Prog) (state : State C F)
    (notType : (DataSem.evaluate program state).1 ≠ some (.err (.abort .typeError)))
    (stopped : (DataSem.evaluate program state).1 ≠ none) :
    ∃ localsSize stackMax safe peak,
      DataSem.evaluate (optimise program) state =
        ((DataSem.evaluate program state).1,
          { (DataSem.evaluate program state).2 with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) := by
  let simplified := DataSimp.simp (DataLive.compile program .ln).1 .skip
  obtain ⟨localsSize, stackMax, safe, peak, liveSimp⟩ := live_simp_correct program state notType stopped
  have stageNotType : (DataSem.evaluate simplified state).1 ≠ some (.err (.abort .typeError)) := by
    simpa only [simplified, liveSimp] using notType
  have stageStopped : (DataSem.evaluate simplified state).1 ≠ none := by
    simpa only [simplified, liveSimp] using stopped
  obtain ⟨safe', peak', stackMax', spaceCorrect⟩ := DataSpace.compile_correct simplified state stageNotType stageStopped
  refine ⟨localsSize, stackMax', safe', peak', ?_⟩
  simpa [optimise, simplified, liveSimp] using spaceCorrect

/-- A singleton expression simulation also covers the optimized function
body used in the data code tree. The unoptimized final state is retained to
state the simulation outcome; the actual optimized state differs only in the
four resource fields allowed by optimization. This composition has no
separate HOL declaration and awaits evaluator and carrier review. -/
theorem compileExp_of_simulation {C F : Type} (body : Bvi.Exp)
    (env : List BvlSem.Value) (source nextSource : BviSem.BviState C F)
    (res : BviSem.BviResult) (target : State C F)
    (ih : simulationFor [body] env source)
    (run : BviSem.evaluate [body] env source = (res, nextSource))
    (notType : res ≠ .err (.abort .typeError))
    (vars : DataProps.varCorr env (List.range env.length) (sptMap dataToBviValue target.locals))
    (fresh : ∀ k, env.length ≤ k → sptLookup k target.locals = none)
    (related : stateRel source target)
    (exceptionJump : isException res → DataSem.jumpExc target ≠ none) :
    ∃ result final names next ls localsSize stackMax safe peak,
      DataSem.evaluate (compileExp env.length body) target =
        (some result, { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) ∧
      stateRel nextSource final ∧
      stateRel nextSource { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak } ∧
      correctOutcome res target final env.length next (List.range env.length) [] names env true (some result) ls := by
  obtain ⟨final, prog, pres, names, next, ls, compiled, targetRun, finalRel, outcome⟩ :=
    ih res nextSource target env.length (List.range env.length) true [] run notType vars (by simp)
      fresh related (by simp) exceptionJump
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    have resultNotType : result ≠ .err (.abort .typeError) := by
      intro eq
      subst result
      have notReturn : ¬ isReturn res := by
        intro returns
        obtain ⟨values, impossible, _⟩ := outcome.2.1 returns
        cases impossible
      exact notType (by simpa [dataToBviResult] using (outcome.1 notReturn).symm)
    have compiledBody : (compileSing env.length (List.range env.length) true [] body).1 = prog := by
      have first := congrArg Prod.fst compiled
      simpa [compileSource_agrees] using first
    obtain ⟨localsSize, stackMax, safe, peak, optimised⟩ :=
      optimise_correct prog target (by simpa [targetRun] using resultNotType) (by simp [targetRun])
    refine ⟨result, final, names, next, ls, localsSize, stackMax, safe, peak, ?_, finalRel, ?_, outcome⟩
    · simpa [compileExp, compiledBody, targetRun] using optimised
    · simpa [stateRel] using finalRel

end Flapjack.Compiler.Backend.BviToData
