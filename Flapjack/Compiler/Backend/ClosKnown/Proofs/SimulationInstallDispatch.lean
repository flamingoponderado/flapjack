module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationInstall

@[expose] public section


/-! Installation outcomes in the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Install
open ClosSem ClosProps Relations Relations.StateRelation BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- A non-type-error installation relates the resulting states and preserves
the post-installation approximation and oracle invariants. In particular,
this includes the timeout path, which advances the compiler oracle before
returning. This is Flapjack proof infrastructure for installation dispatch. -/
theorem installNonTypeInvariants {C F : Type} (c : Config)
    (s : State (Spt ValApprox × C) F) (t : State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : Result (List ClosLang.Exp) ClosSem.Value)
    (s1 : State (Spt ValApprox × C) F)
    (state : StateRel c (nextG s) s t)
    (values : List.Forall₂ (ValueRel c (nextG s)) sourceValues targetValues)
    (mono : oracleGapproxSubspt s.compileOracle)
    (unique : uniqueSetGlobals [] s.compileOracle)
    (globals : stateGlobalsApprox s (nextG s))
    (disjoint : stateOracleMglobalsDisjoint s)
    (oracleDisjoint : oracleGapproxDisjoint (nextG s) s.compileOracle)
    (oracle : isStateOracle (compileInc c) s.compileOracle)
    (run : doInstall sourceValues s = (result, s1))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ targetResult t1 program, ∃ (eas : List (ClosLang.Exp × ValApprox)),
      doInstall targetValues t = (targetResult, t1) ∧
      (result = .err (.abort .timeoutError) ∧ targetResult = .err (.abort .timeoutError) ∨
        result = .val program ∧ targetResult = .val (eas.map Prod.fst)) ∧
      StateRel c (nextG s1) s1 t1 ∧ stateGlobalsApprox s1 (nextG s1) ∧
      isStateOracle (compileInc c) s1.compileOracle ∧
      oracleGapproxDisjoint (nextG s1) s1.compileOracle := by
  obtain ⟨targetResult, t1, program, eas, tree, next, targetRun, known,
    programEq, treeEq, outcome, nextEq, states⟩ :=
    relatedInstallNonType c s t sourceValues targetValues result s1 state mono values run noType
  subst tree
  have programDisjoint : mglobalsDisjoint s.globals program := by
    rw [programEq]
    exact disjoint 0
  have after := ApproxEvaluate.stateGlobalsApproxKnownDisjoint (resetInlineFactor c)
    program [] (nextG s) eas next s ⟨known, programDisjoint, globals⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, _⟩ :=
    doInstall_nonType_parts sourceValues s s1 result run noType
  have afterGlobals : stateGlobalsApprox s1 (nextG s1) := by
    rw [nextEq, final]
    simpa [stateGlobalsApprox] using after
  have afterOracle : isStateOracle (compileInc c) s1.compileOracle := by
    rw [final]
    intro n
    simpa [Flapjack.holShiftSeq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using oracle (n + 1)
  have afterDisjoint : oracleGapproxDisjoint (nextG s1) s1.compileOracle := by
    rw [nextEq, final]
    apply oracleGapproxDisjointInstall (resetInlineFactor c) s.compileOracle (nextG s) eas next
    exact ⟨by simpa [programEq] using known, unique, oracleDisjoint⟩
  exact ⟨targetResult, t1, program, eas, targetRun, outcome, states, afterGlobals, afterOracle, afterDisjoint⟩

/-- The last elements of related nonempty lists are related. This is
Flapjack infrastructure for installation's return value. -/
theorem relatedLast {α β : Type} [Nonempty α] [Nonempty β] (r : α → β → Prop)
    (xs : List α) (ys : List β) (related : List.Forall₂ r xs ys) (nonempty : xs ≠ []) :
    r (Flapjack.holLast xs) (Flapjack.holLast ys) := by
  induction related with
  | nil => exact (nonempty rfl).elim
  | @cons x y xs ys head tail ih =>
    cases tail with
    | nil => simpa [Flapjack.holLast] using head
    | cons next rest =>
      rw [Flapjack.holLastCons.2, Flapjack.holLastCons.2]
      exact ih (by simp)

/-- Installation returns the last value of a successful nonempty installed
program, while preserving errors. This is Flapjack proof infrastructure. -/
noncomputable def installReturn (result : Result (List ClosSem.Value) ClosSem.Value) :
    Result (List ClosSem.Value) ClosSem.Value :=
  match result with
  | .err error => .err error
  | .val values => .val [@Flapjack.holLast ClosSem.Value ⟨unitValue⟩ values]

/-- Successful installation and installed-program evaluation preserve the
result actually returned by the Install operation. This is Flapjack proof
infrastructure for the enclosing operation case. -/
theorem installedProgramReturnSimulation {C F : Type} (c : Config)
    (s : State (Spt ValApprox × C) F) (t : State C F)
    (sourceValues targetValues : List ClosSem.Value) (program : List ClosLang.Exp)
    (s1 final : State (Spt ValApprox × C) F)
    (res : Result (List ClosSem.Value) ClosSem.Value)
    (state : StateRel c (nextG s) s t)
    (safe : StateGlobalSafety.ssgcFree s)
    (oracleSyntax : coEveryFnVarsNone s.compileOracle)
    (oracleSafe : StateRelation.Oracle.oracleStateSgcFree s.compileOracle)
    (disjoint : stateOracleMglobalsDisjoint s)
    (mono : oracleGapproxSubspt s.compileOracle)
    (unique : uniqueSetGlobals [] s.compileOracle)
    (globals : stateGlobalsApprox s (nextG s))
    (oracleDisjoint : oracleGapproxDisjoint (nextG s) s.compileOracle)
    (oracleState : isStateOracle (compileInc c) s.compileOracle)
    (values : List.Forall₂ (ValueRel c (nextG s)) sourceValues targetValues)
    (install : doInstall sourceValues s = (.val program, s1))
    (ih : KnownSimulationAt program [] s1)
    (run : evaluate program [] s1 = (res, final)) (noType : res ≠ .err (.abort .typeError)) :
    ∃ targetProgram t1 targetResult targetFinal,
      doInstall targetValues t = (.val targetProgram, t1) ∧
      evaluate targetProgram [] t1 = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final))
        (installReturn res) (installReturn targetResult) ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧ oracleGapproxDisjoint (nextG final) final.compileOracle := by
  obtain ⟨targetProgram, t1, targetResult, targetFinal, targetInstall, targetRun,
    related, finalState, finalGlobals, finalOracle, finalDisjoint⟩ :=
    installedProgramSimulation c s t sourceValues targetValues program s1 final res state safe
      oracleSyntax oracleSafe disjoint mono unique globals oracleDisjoint oracleState values install ih run noType
  have programNonempty := (installedProgramPreconditions c (nextG s) s t sourceValues program s1
    state safe oracleSyntax oracleSafe disjoint mono install).2.2.1
  let _ : Nonempty ClosSem.Value := ⟨unitValue⟩
  have returnRelated : resultRel (List.Forall₂ (ValueRel c (nextG final)))
      (ValueRel c (nextG final)) (installReturn res) (installReturn targetResult) := by
    cases res with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err other => exact related
    | val resultValues =>
      cases targetResult with
      | err error => simp [resultRel] at related
      | val targetValues =>
        have valuesNonempty : resultValues ≠ [] := by
          intro empty
          subst resultValues
          have len := evaluate_length.1 program [] s1 final [] run
          simp at len
          exact programNonempty (List.eq_nil_of_length_eq_zero len.symm)
        exact List.Forall₂.cons (relatedLast (ValueRel c (nextG final)) resultValues targetValues related valuesNonempty) .nil
  exact ⟨targetProgram, t1, targetResult, targetFinal, targetInstall, targetRun, returnRelated,
    finalState, finalGlobals, finalOracle, finalDisjoint⟩

/-- Simulate installation dispatch after successful related argument
evaluations, including timeout and the installed-program execution. This is
Flapjack infrastructure for the full operation induction case. -/
theorem installDispatchAfterArguments {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (xs ys : List ClosLang.Exp) (env targetEnv : List ClosSem.Value)
    (initial middle : State (Spt ValApprox × C) F) (targetInitial target : State C F)
    (args targetArgs : List ClosSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (final : State (Spt ValApprox × C) F)
    (runArgs : evaluate xs env initial = (.val args, middle))
    (targetRunArgs : evaluate ys targetEnv targetInitial = (.val targetArgs, target))
    (states : StateRel c (nextG middle) middle target)
    (argsRelated : List.Forall₂ (ValueRel c (nextG middle)) args targetArgs)
    (safe : StateGlobalSafety.ssgcFree middle)
    (oracleSyntax : coEveryFnVarsNone middle.compileOracle)
    (oracleSafe : StateRelation.Oracle.oracleStateSgcFree middle.compileOracle)
    (disjoint : stateOracleMglobalsDisjoint middle)
    (mono : oracleGapproxSubspt middle.compileOracle)
    (unique : uniqueSetGlobals [] middle.compileOracle)
    (globals : stateGlobalsApprox middle (nextG middle))
    (oracleDisjoint : oracleGapproxDisjoint (nextG middle) middle.compileOracle)
    (oracle : isStateOracle (compileInc c) middle.compileOracle)
    (ih : ∀ program installed, doInstall args.reverse middle = (.val program, installed) →
      KnownSimulationAt program [] installed)
    (run : evaluate [.op trace .install xs] env initial = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ result' targetFinal,
      evaluate [.op trace .install ys] targetEnv targetInitial = (result', targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) result result' ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  rw [evaluate, fixClock_evaluate, runArgs] at run
  dsimp only at run
  cases sourceInstall : doInstall args.reverse middle with
  | mk installResult installed =>
    rw [sourceInstall] at run
    cases installResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨targetResult, targetInstalled, program, eas, targetInstall, outcome,
        finalState, finalGlobals, finalOracle, finalDisjoint⟩ :=
        installNonTypeInvariants c middle target args.reverse targetArgs.reverse (.err error) installed
          states (List.rel_reverse argsRelated) mono unique globals disjoint oracleDisjoint oracle
          sourceInstall (by intro h; cases h; exact noType rfl)
      rcases outcome with ⟨sourceError, targetError⟩ | ⟨impossible, _⟩
      · cases sourceError
        subst targetResult
        refine ⟨.err (.abort .timeoutError), targetInstalled, ?_, ?_, finalState, finalGlobals, finalOracle, finalDisjoint⟩
        · rw [evaluate, fixClock_evaluate, targetRunArgs]
          dsimp only
          rw [targetInstall]
        · simp [resultRel, excRel]
      · cases impossible
    | val program =>
      dsimp only at run
      cases bodyRun : evaluate program [] installed with
      | mk bodyResult last =>
        rw [bodyRun] at run
        have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
          intro eq
          subst bodyResult
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact noType rfl
        obtain ⟨targetProgram, targetInstalled, targetBodyResult, targetLast, targetInstall,
          targetBodyRun, resultRelated, finalState, finalGlobals, finalOracle, finalDisjoint⟩ :=
          installedProgramReturnSimulation c middle target args.reverse targetArgs.reverse program
            installed last bodyResult states safe oracleSyntax oracleSafe disjoint mono unique globals
            oracleDisjoint oracle (List.rel_reverse argsRelated) sourceInstall
            (ih program installed sourceInstall) bodyRun bodyNoType
        cases bodyResult with
        | err error =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          cases targetBodyResult with
          | val vals => simp [installReturn, resultRel] at resultRelated
          | err targetError =>
            refine ⟨.err targetError, targetLast, ?_, resultRelated, finalState, finalGlobals, finalOracle, finalDisjoint⟩
            rw [evaluate, fixClock_evaluate, targetRunArgs]
            dsimp only
            rw [targetInstall]
            dsimp only
            rw [targetBodyRun]
        | val vals =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          cases targetBodyResult with
          | err error => simp [installReturn, resultRel] at resultRelated
          | val targetVals =>
            refine ⟨installReturn (.val targetVals), targetLast, ?_, resultRelated,
              finalState, finalGlobals, finalOracle, finalDisjoint⟩
            rw [evaluate, fixClock_evaluate, targetRunArgs]
            dsimp only
            rw [targetInstall]
            dsimp only
            rw [targetBodyRun]
            rfl


end Flapjack.Compiler.Backend.ClosKnown.Simulation.Install
