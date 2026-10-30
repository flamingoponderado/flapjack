import Flapjack.Compiler.Backend.ClosInterp.Proofs.ForceRelation

/-! Dynamic-installation simulation for the proof-side evaluator. The
semantics and finite-map carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

/-- Updating a finite map with no entries leaves it unchanged. -/
theorem finiteMap_updateListEq_nil {α β : Type} [DecidableEq α] (map : HolFiniteMapExact α β) :
    map.updateListEq [] = map := by
  cases map
  simp [HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL]

/-- Interpreter insertion preserves whether a program is empty. -/
theorem insertInterp_eq_nil (expressions : List ClosLang.Exp) :
    insertInterp expressions = [] ↔ expressions = [] := by
  simp [insertInterp]

/-- Related installation oracles supply the same configuration, with
interpreter insertion applied to the target expressions. -/
theorem stateRel_oracle_head {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (config : C) (expressions : List ClosLang.Exp)
    (oracle : source.compileOracle 0 = (config, (expressions, []))) :
    target.compileOracle 0 = (config, (insertInterp expressions, [])) := by
  have rel := related.1.2.2.2.2.2.2.2.2.2.2
  rw [rel]
  simp [oracle, pureCo, insertProgram]

/-- Related compilers agree on the corresponding installation request. -/
theorem stateRel_compile {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (config : C) (expressions : List ClosLang.Exp) :
    source.compile config (expressions, []) = target.compile config (insertInterp expressions, []) := by
  have rel := related.1.2.2.2.2.2.2.2.2.2.1
  rw [rel]
  rfl

/-- Shifting related oracles and consuming equal clock preserves the state relation. -/
theorem stateRel_installNext {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) :
    StateRel { source with code := source.code.updateListEq [], compileOracle := Flapjack.holShiftSeq 1 source.compileOracle, clock := source.clock - 1 }
      { target with code := target.code.updateListEq [], compileOracle := Flapjack.holShiftSeq 1 target.compileOracle, clock := target.clock - 1 } := by
  have shifted := stateRel_shift related 1
  have clockEq : target.clock = source.clock := related.1.2.2.2.2.2.1
  have shiftedClock := stateRel_withClock shifted (source.clock - 1)
  simpa [finiteMap_updateListEq_nil, clockEq] using shiftedClock

/-- Non-type-error installation outcomes correspond in related states. -/
theorem doInstall_stateRel {C F : Type} (values : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosLang.Exp) ClosSem.Value)
    (related : StateRel source target) (run : ClosSem.doInstall values source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetResult targetFinal,
      ClosSem.doInstall values target = (targetResult, targetFinal) ∧ StateRel sourceFinal targetFinal ∧
      (match result with
       | .err error => targetResult = .err error
       | .val expressions => targetResult = .val (insertInterp expressions)) := by
  classical
  have safe := related.1.1 0
  cases sourceHead : source.compileOracle 0 with
  | mk config program =>
    cases program with
    | mk expressions auxiliary =>
      simp [sourceHead] at safe
      subst auxiliary
      have targetHead := stateRel_oracle_head source target related config expressions sourceHead
      have compilerEq := stateRel_compile source target related config expressions
      have clockEq : target.clock = source.clock := related.1.2.2.2.2.2.1
      cases values with
      | nil => simp [ClosSem.doInstall] at run; exact (notTypeError run.1.symm).elim
      | cons bytesValue rest =>
        cases rest with
        | nil => simp [ClosSem.doInstall] at run; exact (notTypeError run.1.symm).elim
        | cons wordsValue rest =>
          cases rest with
          | cons other rest => simp [ClosSem.doInstall] at run; exact (notTypeError run.1.symm).elim
          | nil =>
            cases bytesRun : ClosSem.valueToBytes bytesValue with
            | none => simp [ClosSem.doInstall, bytesRun] at run; exact (notTypeError run.1.symm).elim
            | some bytes =>
              cases wordsRun : ClosSem.valueToWords wordsValue with
              | none => simp [ClosSem.doInstall, bytesRun, wordsRun] at run; exact (notTypeError run.1.symm).elim
              | some words =>
                cases compileRun : source.compile config (expressions, []) with
                | none =>
                  simp [ClosSem.doInstall, bytesRun, wordsRun, sourceHead, compileRun] at run
                  exact (notTypeError run.1.symm).elim
                | some output =>
                  rcases output with ⟨compiledBytes, compiledWords, nextConfig⟩
                  have targetCompile : target.compile config (insertInterp expressions, []) = some (compiledBytes, compiledWords, nextConfig) := by
                    rw [← compilerEq]
                    exact compileRun
                  have shiftConfig : (Flapjack.holShiftSeq 1 target.compileOracle 0).1 =
                      (Flapjack.holShiftSeq 1 source.compileOracle 0).1 := by
                    have oracleRel := related.1.2.2.2.2.2.2.2.2.2.2
                    rw [oracleRel]
                    simp [Flapjack.holShiftSeq, pureCo]
                  by_cases valid : bytes = compiledBytes ∧ words = compiledWords ∧
                      (Flapjack.holShiftSeq 1 source.compileOracle 0).1 = nextConfig ∧ expressions ≠ []
                  · have targetValid : bytes = compiledBytes ∧ words = compiledWords ∧
                        (Flapjack.holShiftSeq 1 target.compileOracle 0).1 = nextConfig ∧ insertInterp expressions ≠ [] := by
                      rcases valid with ⟨bytesEq, wordsEq, configEq, nonempty⟩
                      exact ⟨bytesEq, wordsEq, shiftConfig.trans configEq, fun h => nonempty (insertInterp_eq_nil expressions |>.mp h)⟩
                    have nextRel := stateRel_installNext source target related
                    by_cases zero : source.clock = 0
                    · have sourceResult : ClosSem.doInstall [bytesValue, wordsValue] source =
                          (.err (.abort .timeoutError), { source with code := source.code.updateListEq [], compileOracle := Flapjack.holShiftSeq 1 source.compileOracle, clock := source.clock - 1 }) := by
                        simp [ClosSem.doInstall, bytesRun, wordsRun, sourceHead, compileRun, valid, zero]
                      rw [sourceResult] at run
                      cases run
                      refine ⟨.err (.abort .timeoutError), _, ?_, nextRel, rfl⟩
                      simp [ClosSem.doInstall, bytesRun, wordsRun, targetHead, targetCompile, targetValid, clockEq, zero]
                    · have sourceResult : ClosSem.doInstall [bytesValue, wordsValue] source =
                          (.val expressions, { source with code := source.code.updateListEq [], compileOracle := Flapjack.holShiftSeq 1 source.compileOracle, clock := source.clock - 1 }) := by
                        simp [ClosSem.doInstall, bytesRun, wordsRun, sourceHead, compileRun, valid, zero]
                      rw [sourceResult] at run
                      cases run
                      refine ⟨.val (insertInterp expressions), _, ?_, nextRel, rfl⟩
                      simp [ClosSem.doInstall, bytesRun, wordsRun, targetHead, targetCompile, targetValid, clockEq, zero]
                  · simp [ClosSem.doInstall, bytesRun, wordsRun, sourceHead, compileRun, valid] at run
                    exact (notTypeError run.1.symm).elim

/-- Installation simulation from the argument and installed-program
induction hypotheses. -/
theorem evaluate_install_simulation_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ∀ (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (result, sourceFinal) → StateRel source target →
      result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate args env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (installedIH : ∀ (program : List ClosLang.Exp) (installedSource installedTarget installedFinal : ClosSem.State C F)
      (installedResult : Result (List ClosSem.Value) ClosSem.Value),
      installedSource.clock < source.clock →
      ClosSem.evaluate program [] installedSource = (installedResult, installedFinal) →
      StateRel installedSource installedTarget → installedResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate (insertInterp program) [] { installedTarget with clock := extra + installedTarget.clock } =
          (installedResult, targetFinal) ∧ StateRel installedFinal targetFinal)
    (related : StateRel source target)
    (run : ClosSem.evaluate [.op trace .install args] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [.op trace .install args] env { target with clock := extra + target.clock } =
        (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases argsRun : ClosSem.evaluate args env source with
  | mk argsResult sourceMid =>
    have bound : sourceMid.clock ≤ source.clock := by
      have h := ClosSem.evaluate_clock_le args env source
      simpa [argsRun] using h
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun] at run
    have argsNotTypeError : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨argsExtra, targetMid, targetArgs, midRel⟩ := argsIH source target sourceMid argsResult argsRun related argsNotTypeError
    cases argsResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨argsExtra, targetMid, ?_, midRel⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
    | val values =>
      dsimp only at run
      cases installRun : ClosSem.doInstall values.reverse sourceMid with
      | mk installResult sourceInstalled =>
        rw [installRun] at run
        have installNotTypeError : installResult ≠ .err (.abort .typeError) := by
          intro bad
          subst installResult
          simp at run
          exact notTypeError run.1.symm
        obtain ⟨targetInstallResult, targetInstalled, targetInstall, installedRel, resultRel⟩ :=
          doInstall_stateRel values.reverse sourceMid targetMid sourceInstalled installResult midRel installRun installNotTypeError
        cases installResult with
        | err error =>
          simp at resultRel run
          subst targetInstallResult
          rcases run with ⟨rfl, rfl⟩
          refine ⟨argsExtra, targetInstalled, ?_, installedRel⟩
          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
          dsimp only
          rw [targetInstall]
        | val program =>
          simp at resultRel
          subst targetInstallResult
          dsimp only at run
          cases programRun : ClosSem.evaluate program [] sourceInstalled with
          | mk programResult sourceLast =>
            rw [programRun] at run
            have programNotTypeError : programResult ≠ .err (.abort .typeError) := by
              intro bad
              subst programResult
              simp at run
              exact notTypeError run.1.symm
            have clock := ClosSem.doInstall_success_clock values.reverse sourceMid sourceInstalled program installRun
            have smaller : sourceInstalled.clock < source.clock := by omega
            obtain ⟨programExtra, targetLast, targetProgram, lastRel⟩ :=
              installedIH program sourceInstalled targetInstalled sourceLast programResult smaller programRun installedRel programNotTypeError
            have shiftedArgs := ClosSem.evaluate_addClock.1 args env
              { target with clock := argsExtra + target.clock } targetMid (.val values) programExtra targetArgs (by simp)
            let enlarged := { target with clock := (argsExtra + target.clock) + programExtra }
            let enlargedMid := { targetMid with clock := targetMid.clock + programExtra }
            let enlargedInstalled := { targetInstalled with clock := targetInstalled.clock + programExtra }
            have targetArgs' : ClosSem.evaluate args env enlarged = (.val values, enlargedMid) := by
              simpa [enlarged, enlargedMid] using shiftedArgs
            have targetInstall' : ClosSem.doInstall values.reverse enlargedMid =
                (.val (insertInterp program), enlargedInstalled) := by
              simpa [enlargedMid, enlargedInstalled] using
                ClosSem.doInstall_success_addClock values.reverse targetMid targetInstalled (insertInterp program) programExtra targetInstall
            have targetProgram' : ClosSem.evaluate (insertInterp program) [] enlargedInstalled =
                (programResult, targetLast) := by
              simpa [enlargedInstalled, Nat.add_comm] using targetProgram
            cases programResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨argsExtra + programExtra, targetLast, ?_, lastRel⟩
              have targetRun : ClosSem.evaluate [.op trace .install args] env enlarged = (.err error, targetLast) := by
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs']
                dsimp only
                rw [targetInstall']
                dsimp only
                rw [targetProgram']
              simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetRun
            | val programValues =>
              change (.val [@Flapjack.holLast ClosSem.Value ⟨ClosSem.unitValue⟩ programValues], sourceLast) = (result, sourceFinal) at run
              cases run
              refine ⟨argsExtra + programExtra, targetLast, ?_, lastRel⟩
              have targetRun : ClosSem.evaluate [.op trace .install args] env enlarged =
                  (.val [@Flapjack.holLast ClosSem.Value ⟨ClosSem.unitValue⟩ programValues], targetLast) := by
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs']
                dsimp only
                rw [targetInstall']
                dsimp only
                rw [targetProgram']
                rfl
              simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetRun

end Flapjack.Compiler.Backend.ClosInterp
