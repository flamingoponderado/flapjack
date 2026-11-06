import Flapjack.Compiler.Backend.FlatPattern.Proofs.ClockedExpressionList

/-! Clock-bounded expression cases for flat pattern compilation. The evaluator
and proof-side relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- An unbounded expression simulation holds at any clock bound. -/
theorem expressionSimulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (expression : FlatLang.Exp)
    (sim : ExpressionSimulation (C := C) (F := F) cfg stateCfg expression) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n _ run envs states bound safe
  exact sim sourceEnv targetEnv source target sourceFinal sourceResult n run envs states bound safe


/-- Clock-bounded version of the corresponding expression case. -/
theorem compile_raise_simulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (trace : BackendCommon.Tra)
    (body : FlatLang.Exp) (bodyIH : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock body) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.raise trace body) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
  cases compiled : compileExp cfg body with
  | mk bodyBound rest =>
    cases rest with
    | mk flag compiledBody =>
      have smaller : bodyBound < n := by simpa [compileExp, compiled] using bound
      cases bodyRun : FlatSem.evaluate sourceEnv source [body] with
      | mk sourceNext bodyResult =>
        have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
          intro bad
          subst bodyResult
          have outer := evaluate_raise_error trace body sourceEnv source sourceNext (.abort .typeError) bodyRun
          rw [sourceEval] at outer
          exact safe (congrArg Prod.snd outer)
        obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ :=
          bodyIH sourceEnv targetEnv source target sourceNext bodyResult n clockBound bodyRun envs states (by simpa [compiled] using smaller) bodySafe
        cases related with
        | error errorsRel =>
          rename_i leftError rightError
          have sourceOuter := evaluate_raise_error trace body sourceEnv source sourceNext leftError bodyRun
          have targetOuter := evaluate_raise_error trace compiledBody targetEnv target targetNext rightError (by simpa [compiled] using targetRun)
          have equal := sourceEval.symm.trans sourceOuter
          cases equal
          exact ⟨targetNext, .err rightError, by simpa [compileExp, compiled] using targetOuter, nextStates, .error errorsRel⟩
        | values valuesRel =>
          rename_i sourceValues targetValues
          obtain ⟨value, valueEq⟩ := singletonSuccess body sourceEnv source sourceNext sourceValues bodyRun
          subst sourceValues
          cases valuesRel with
          | cons valueRel tailRel =>
            cases tailRel
            rename_i value'
            have sourceOuter := evaluate_raise_value trace body sourceEnv source sourceNext value bodyRun
            have targetOuter := evaluate_raise_value trace compiledBody targetEnv target targetNext value' (by simpa [compiled] using targetRun)
            have equal := sourceEval.symm.trans sourceOuter
            cases equal
            exact ⟨targetNext, .err (.raise value'), by simpa [compileExp, compiled] using targetOuter,
              nextStates, .error (.raise valueRel)⟩


/-- Clock-bounded version of the corresponding expression case. -/
theorem compile_if_simulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (trace : BackendCommon.Tra)
    (condition yes no : FlatLang.Exp)
    (conditionIH : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock condition)
    (yesIH : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock yes)
    (noIH : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock no) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.if_ trace condition yes no) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
  cases c : compileExp cfg condition with
  | mk ci crest =>
    cases crest with
    | mk cf ce =>
      cases y : compileExp cfg yes with
      | mk yi yrest =>
        cases yrest with
        | mk yf ye =>
          cases z : compileExp cfg no with
          | mk zi zrest =>
            cases zrest with
            | mk zf ze =>
              have bounds : ci < n ∧ yi < n ∧ zi < n := by
                simp [compileExp, c, y, z] at bound
                omega
              cases conditionRun : FlatSem.evaluate sourceEnv source [condition] with
              | mk sourceNext conditionResult =>
                have conditionSafe : conditionResult ≠ .err (.abort .typeError) := by
                  intro bad
                  subst conditionResult
                  have outer := evaluate_if_error trace condition yes no sourceEnv source sourceNext (.abort .typeError) conditionRun
                  rw [sourceEval] at outer
                  exact safe (congrArg Prod.snd outer)
                obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := conditionIH
                  sourceEnv targetEnv source target sourceNext conditionResult n clockBound conditionRun envs states (by simpa [c] using bounds.1) conditionSafe
                cases related with
                | error errorsRel =>
                  rename_i leftError rightError
                  have sourceOuter := evaluate_if_error trace condition yes no sourceEnv source sourceNext leftError conditionRun
                  have targetOuter := evaluate_if_error trace ce ye ze targetEnv target targetNext rightError (by simpa [c] using targetRun)
                  have equal := sourceEval.symm.trans sourceOuter
                  cases equal
                  exact ⟨_, _, by simpa [compileExp, c, y, z, evaluate_smartIf] using targetOuter,
                    stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, .error errorsRel⟩
                | values valuesRel =>
                  rename_i sourceValues targetValues
                  obtain ⟨value, valueEq⟩ := singletonSuccess condition sourceEnv source sourceNext sourceValues conditionRun
                  subst sourceValues
                  cases valuesRel with
                  | cons valueRel tailRel =>
                    cases tailRel
                    rename_i value'
                    let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
                    let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
                    have fixedStates := stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
                    cases selected : FlatSem.doIf value yes no with
                    | none =>
                      have bad := evaluate_if_bad trace condition yes no sourceEnv source sourceNext value conditionRun selected
                      rw [sourceEval] at bad
                      exact (safe (congrArg Prod.snd bad)).elim
                    | some branch =>
                      have same := doIf_related value value' yes no branch valueRel selected
                      have sourceOuter := evaluate_if_selected trace condition yes no branch sourceEnv source sourceNext value conditionRun selected
                      have sourceBranch := sourceOuter.symm.trans sourceEval
                      have choice := FlatSem.doIf_selected value yes no branch selected
                      rcases choice with choice | choice
                      · subst branch
                        have targetSelected : FlatSem.doIf value' ye ze = some ye := by
                          have mapped := doIf_map (fun expression => (compileExp cfg expression).2.2) value' yes no
                          simpa [same, y, z] using mapped
                        have targetOuter := evaluate_if_selected trace ce ye ze ye targetEnv target targetNext value'
                          (by simpa [c] using targetRun) targetSelected
                        obtain ⟨targetFinal, output, branchRun, finalRel, resultRel⟩ := yesIH
                          sourceEnv targetEnv sourceFixed targetFixed sourceFinal sourceResult n (by dsimp [sourceFixed]; omega) sourceBranch envs fixedStates
                          (by simpa [y] using bounds.2.1) safe
                        refine ⟨targetFinal, output, ?_, finalRel, resultRel⟩
                        simpa [compileExp, c, y, z, evaluate_smartIf, targetOuter] using branchRun
                      · subst branch
                        have targetSelected : FlatSem.doIf value' ye ze = some ze := by
                          have mapped := doIf_map (fun expression => (compileExp cfg expression).2.2) value' yes no
                          simpa [same, y, z] using mapped
                        have targetOuter := evaluate_if_selected trace ce ye ze ze targetEnv target targetNext value'
                          (by simpa [c] using targetRun) targetSelected
                        obtain ⟨targetFinal, output, branchRun, finalRel, resultRel⟩ := noIH
                          sourceEnv targetEnv sourceFixed targetFixed sourceFinal sourceResult n (by dsimp [sourceFixed]; omega) sourceBranch envs fixedStates
                          (by simpa [z] using bounds.2.2) safe
                        refine ⟨targetFinal, output, ?_, finalRel, resultRel⟩
                        simpa [compileExp, c, y, z, evaluate_smartIf, targetOuter] using branchRun


/-- Clock-bounded version of the corresponding expression case. -/
theorem compile_let_simulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (trace : BackendCommon.Tra)
    (name : Option VarN) (first body : FlatLang.Exp)
    (firstIH : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock first)
    (bodyIH : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock body) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.let_ trace name first body) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
  cases c : compileExp cfg first with
  | mk ci crest =>
    cases crest with
    | mk cf ce =>
      cases b : compileExp cfg body with
      | mk bi brest =>
        cases brest with
        | mk bf be =>
          have bounds : ci < n ∧ bi < n := by
            simp [compileExp, c, b] at bound
            omega
          cases firstRun : FlatSem.evaluate sourceEnv source [first] with
          | mk sourceNext firstResult =>
            have firstSafe : firstResult ≠ .err (.abort .typeError) := by
              intro bad
              subst firstResult
              have outer := evaluate_let_error_any trace name first body sourceEnv source sourceNext (.abort .typeError) firstRun
              rw [sourceEval] at outer
              exact safe (congrArg Prod.snd outer)
            obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := firstIH
              sourceEnv targetEnv source target sourceNext firstResult n clockBound firstRun envs states (by simpa [c] using bounds.1) firstSafe
            cases related with
            | error errorsRel =>
              rename_i leftError rightError
              have sourceOuter := evaluate_let_error_any trace name first body sourceEnv source sourceNext leftError firstRun
              have targetOuter := evaluate_let_error_any trace name ce be targetEnv target targetNext rightError (by simpa [c] using targetRun)
              have equal := sourceEval.symm.trans sourceOuter
              cases equal
              exact ⟨_, _, by simpa [compileExp, c, b] using targetOuter,
                stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, .error errorsRel⟩
            | values valuesRel =>
              rename_i sourceValues targetValues
              obtain ⟨value, valueEq⟩ := singletonSuccess first sourceEnv source sourceNext sourceValues firstRun
              subst sourceValues
              cases valuesRel with
              | cons valueRel tailRel =>
                cases tailRel
                rename_i value'
                let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
                let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
                have fixedStates := stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
                cases name with
                | none =>
                  have sourceOuter := evaluate_let_value trace none first body sourceEnv source sourceNext value firstRun
                  have targetOuter := evaluate_let_value trace none ce be targetEnv target targetNext value' (by simpa [c] using targetRun)
                  obtain ⟨targetFinal, output, bodyRun, finalRel, resultRel⟩ := bodyIH
                    sourceEnv targetEnv sourceFixed targetFixed sourceFinal sourceResult n (by dsimp [sourceFixed]; omega) (by simpa using sourceOuter.symm.trans sourceEval)
                    envs fixedStates (by simpa [b] using bounds.2) safe
                  refine ⟨targetFinal, output, ?_, finalRel, resultRel⟩
                  simpa [compileExp, c, b, targetOuter] using bodyRun
                | some name =>
                  have sourceOuter := evaluate_let_value trace (some name) first body sourceEnv source sourceNext value firstRun
                  have targetOuter := evaluate_let_value trace (some name) ce be targetEnv target targetNext value' (by simpa [c] using targetRun)
                  have extended := envRel_cons n sourceEnv targetEnv name value value' envs valueRel
                  obtain ⟨targetFinal, output, bodyRun, finalRel, resultRel⟩ := bodyIH
                    { sourceEnv with v := (name, value) :: sourceEnv.v }
                    { targetEnv with v := (name, value') :: targetEnv.v } sourceFixed targetFixed sourceFinal sourceResult n
                    (by dsimp [sourceFixed]; omega) (by simpa using sourceOuter.symm.trans sourceEval) extended fixedStates (by simpa [b] using bounds.2) safe
                  refine ⟨targetFinal, output, ?_, finalRel, resultRel⟩
                  simpa [compileExp, c, b, targetOuter] using bodyRun


/-- Clock-bounded version of the corresponding expression case. -/
theorem compile_letrec_simulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (trace : VarN)
    (funs : List (VarN × VarN × FlatLang.Exp)) (body : FlatLang.Exp)
    (bodyIH : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock body) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.letrec trace funs body) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
  cases f : compileFuns cfg funs with
  | mk fi frest =>
    cases frest with
    | mk ff fs =>
      cases b : compileExp cfg body with
      | mk bi brest =>
        cases brest with
        | mk bf be =>
          have bounds : fi < n ∧ bi < n := by simp [compileExp, f, b] at bound; omega
          have fsEq : fs = compiledRecFuns cfg funs := by simpa [f] using compileFuns_rows cfg funs
          have funBounds : ∀ entry ∈ funs, (compileExp cfg entry.2.2).1 < n := by
            intro entry member
            have h := compileFuns_member_bound cfg funs entry member
            simp only [f] at h
            omega
          by_cases distinct : (funs.map Prod.fst).Nodup
          · have targetDistinct : (fs.map Prod.fst).Nodup := by simpa [fsEq, compiledRecFuns_names] using distinct
            have relatedEnvs := envRel_buildRec n sourceEnv targetEnv cfg funs envs funBounds
            have sourceBody : FlatSem.evaluate { sourceEnv with v := FlatSem.buildRecEnv funs sourceEnv sourceEnv.v }
                source [body] = (sourceFinal, sourceResult) := by simpa [FlatSem.evaluate, distinct] using sourceEval
            obtain ⟨targetFinal, targetResult, bodyRun, finalRel, resultRel⟩ := bodyIH
              { sourceEnv with v := FlatSem.buildRecEnv funs sourceEnv sourceEnv.v }
              { targetEnv with v := FlatSem.buildRecEnv (compiledRecFuns cfg funs) targetEnv targetEnv.v }
              source target sourceFinal sourceResult n clockBound sourceBody relatedEnvs states (by simpa [b] using bounds.2) safe
            refine ⟨targetFinal, targetResult, ?_, finalRel, resultRel⟩
            simpa [compileExp, f, b, FlatSem.evaluate, fsEq, compiledRecFuns_names, distinct] using bodyRun
          · have bad : sourceResult = .err (.abort .typeError) := by
              simpa [FlatSem.evaluate, distinct] using congrArg Prod.snd sourceEval.symm
            exact (safe bad).elim


/-- Constructor expressions preserve the forward simulation when their
argument expressions satisfy the induction hypotheses. -/
theorem compile_con_simulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (trace : BackendCommon.Tra)
    (tag : Option (FlatLang.CtorId × FlatLang.TypeId)) (args : List FlatLang.Exp)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.con trace tag args) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
  cases compiled : compileExps cfg args with
  | mk argsBound result =>
    cases result with
    | mk flag compiledArgs =>
      have argsBoundLt : (compileExps cfg args).1 < n := by simpa [compileExp, compiled] using bound
      have reversedBound := compileExps_reverse_bound cfg args n argsBoundLt
      have reversedIH : ∀ expression ∈ args.reverse, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression := by
        intro expression member
        exact argumentsIH expression (by simpa using member)
      have listSim := compileExps_simulation_upTo cfg stateCfg clock args.reverse reversedIH
      cases argsRun : FlatSem.evaluate sourceEnv source args.reverse with
      | mk sourceNext argsResult =>
        have argsSafe : argsResult ≠ .err (.abort .typeError) := by
          intro bad
          subst argsResult
          have outer := evaluate_con_error sourceEnv source sourceNext trace tag args (.abort .typeError) argsRun
          rw [sourceEval] at outer
          exact safe (congrArg Prod.snd outer)
        obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := listSim
          sourceEnv targetEnv source target sourceNext argsResult n clockBound argsRun envs states reversedBound argsSafe
        have compiledReverse : (compileExps cfg args.reverse).2.2 = compiledArgs.reverse := by
          have h := compileExps_rows cfg args
          simp only [compiled] at h
          simp [compileExps_rows, ← h, List.map_reverse]
        cases related with
        | error errorsRel =>
          rename_i leftError rightError
          have sourceOuter := evaluate_con_error sourceEnv source sourceNext trace tag args leftError argsRun
          have targetOuter := evaluate_con_error targetEnv target targetNext trace tag compiledArgs rightError (by
            simpa [compiledReverse] using targetRun)
          have equal := sourceEval.symm.trans sourceOuter
          cases equal
          exact ⟨targetNext, _, by simpa [compileExp, compiled] using targetOuter, nextStates, .error errorsRel⟩
        | values valuesRel =>
          rename_i sourceValues targetValues
          have sourceOuter := evaluate_con_values sourceEnv source sourceNext trace tag args sourceValues argsRun
          have targetOuter := evaluate_con_values targetEnv target targetNext trace tag compiledArgs targetValues (by
            simpa [compiledReverse] using targetRun)
          have equal := sourceEval.symm.trans sourceOuter
          cases equal
          have constructorRel : ValueRel (.conv tag sourceValues.reverse) (.conv tag targetValues.reverse) :=
            (valueRel_conv tag _ _).2 ⟨_, rfl, (valueRel_reverse valuesRel)⟩
          exact ⟨targetNext, _, by simpa [compileExp, compiled] using targetOuter,
            nextStates, .values (.cons constructorRel .nil)⟩

/-- Clock-bounded pattern-match case. -/
theorem compile_mat_simulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (scrutineeIH : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock scrutinee)
    (bodiesIH : ∀ pattern body, (pattern, body) ∈ rows → ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock body) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.mat trace scrutinee rows) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
  have generatedBound : max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2 < n := by
    simpa [compileExp_mat_bound] using bound
  have scrutineeBound : (compileExp cfg scrutinee).1 < n := by omega
  cases scrutineeRun : FlatSem.evaluate sourceEnv source [scrutinee] with
  | mk sourceNext scrutineeResult =>
    have scrutineeSafe : scrutineeResult ≠ .err (.abort .typeError) := by
      intro bad
      subst scrutineeResult
      have run := evaluate_mat_error trace scrutinee rows sourceEnv source sourceNext (.abort .typeError) scrutineeRun
      rw [sourceEval] at run
      exact safe (congrArg Prod.snd run)
    obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := scrutineeIH
      sourceEnv targetEnv source target sourceNext scrutineeResult n clockBound scrutineeRun envs states scrutineeBound scrutineeSafe
    cases related with
    | error errorsRel =>
      rename_i sourceError targetError
      have sourceRun := evaluate_mat_error trace scrutinee rows sourceEnv source sourceNext _ scrutineeRun
      have targetRun' : FlatSem.evaluate targetEnv target [(compileExp cfg (.mat trace scrutinee rows)).2.2] =
          ({ targetNext with clock := min target.clock targetNext.clock }, .err targetError) := by
        rw [compileExp_mat_body]
        apply evaluate_let_error
        exact targetRun
      have equal := sourceEval.symm.trans sourceRun
      cases equal
      exact ⟨_, _, targetRun', stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, .error errorsRel⟩
    | values valuesRel =>
      rename_i values values'
      obtain ⟨value, valuesEq⟩ := singletonSuccess scrutinee sourceEnv source sourceNext values scrutineeRun
      subst values
      cases valuesRel with
      | cons valueRel tailRel =>
        cases tailRel
        rename_i value'
        let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
        let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
        have fixedStates : StateRel stateCfg sourceFixed targetFixed :=
          stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
        cases rowResult : FlatSem.pmatchRows rows sourceFixed value with
        | typeError =>
          have run := evaluate_mat_rowTypeError trace scrutinee rows sourceEnv source sourceNext value scrutineeRun rowResult
          rw [sourceEval] at run
          exact (safe (congrArg Prod.snd run)).elim
        | noMatch =>
          obtain ⟨sourceFinal', targetFinal, sourceResult', targetResult', sourceRun, targetRun', finalRel, resultRel⟩ :=
            compile_mat_noMatch_forward cfg stateCfg trace scrutinee rows source sourceNext target targetNext
              sourceEnv targetEnv value value' scrutineeRun targetRun fixedStates valueRel rowResult
          have equal := sourceEval.symm.trans sourceRun
          cases equal
          exact ⟨targetFinal, targetResult', targetRun', finalRel, resultRel⟩
        | «match» selected =>
          rcases selected with ⟨bindings, pattern, body⟩
          have distinct : (FlatLang.patBindings pattern).Nodup := by
            by_cases distinct : (FlatLang.patBindings pattern).Nodup
            · exact distinct
            · have run := evaluate_mat_duplicate trace scrutinee rows sourceEnv source sourceNext value
                bindings pattern body scrutineeRun rowResult distinct
              rw [sourceEval] at run
              exact (safe (congrArg Prod.snd run)).elim
          have sourceBody : FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v } sourceFixed [body] =
              (sourceFinal, sourceResult) := by
            have run := evaluate_mat_selected trace scrutinee rows sourceEnv source sourceNext value
              bindings pattern body scrutineeRun rowResult distinct
            exact run.symm.trans sourceEval
          have member := pmatchRows_match_mem sourceFixed value rows bindings pattern body rowResult
          have bodySim := bodiesIH pattern body member
          let generated := max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2
          have bodyBound : (compileExp cfg body).1 < generated - 1 := by
            have bodyLe := (compileMatch_member_bound cfg rows pattern body member).1
            dsimp [generated]
            omega
          have bodyIH : ∀ extEnv,
              EnvRel (generated - 1) { sourceEnv with v := bindings ++ sourceEnv.v } extEnv →
              FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v } sourceFixed [body] = (sourceFinal, sourceResult) →
              ∃ targetFinal targetResult,
                FlatSem.evaluate extEnv targetFixed [(compileExp cfg body).2.2] = (targetFinal, targetResult) ∧
                StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
            intro extEnv envRel evaluated
            exact bodySim _ _ _ _ _ _ _ (by dsimp [sourceFixed]; omega) evaluated envRel fixedStates bodyBound safe
          obtain ⟨_, targetFinal, targetResult', targetRun', finalRel, resultRel⟩ :=
            compile_mat_selected_forward cfg stateCfg trace scrutinee rows source sourceNext target targetNext sourceFinal
              sourceEnv targetEnv value value' bindings pattern body sourceResult n scrutineeRun targetRun fixedStates
              valueRel envs (by dsimp [generated] at *; omega) rowResult distinct sourceBody bodyIH
          exact ⟨targetFinal, targetResult', targetRun', finalRel, resultRel⟩


/-- Clock-bounded exception-handler case. -/
theorem compile_handle_simulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (protectedIH : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock protectedExpr)
    (bodiesIH : ∀ pattern body, (pattern, body) ∈ rows → ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock body) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.handle trace protectedExpr rows) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
  have generatedBound : max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2 < n := by
    simpa [compileExp_handle_bound] using bound
  have protectedBound : (compileExp cfg protectedExpr).1 < n := by omega
  cases protectedRun : FlatSem.evaluate sourceEnv source [protectedExpr] with
  | mk sourceNext protectedResult =>
    have protectedSafe : protectedResult ≠ .err (.abort .typeError) := by
      intro bad
      subst protectedResult
      have run := evaluate_handle_passthrough trace protectedExpr rows sourceEnv source sourceNext
        (.err (.abort .typeError)) protectedRun (by simp)
      rw [sourceEval] at run
      exact safe (congrArg Prod.snd run)
    obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := protectedIH
      sourceEnv targetEnv source target sourceNext protectedResult n clockBound protectedRun envs states protectedBound protectedSafe
    cases related with
    | values valuesRel =>
      obtain ⟨sourceFinal', targetFinal, sourceRun, targetRun', finalRel⟩ :=
        compile_handle_passthrough cfg stateCfg trace protectedExpr rows source sourceNext target targetNext
          sourceEnv targetEnv _ _ protectedRun targetRun states nextStates (.values valuesRel) (by simp)
      have equal := sourceEval.symm.trans sourceRun
      cases equal
      exact ⟨targetFinal, _, targetRun', finalRel, .values valuesRel⟩
    | error errorRel =>
      cases errorRel with
      | abort reason =>
        obtain ⟨sourceFinal', targetFinal, sourceRun, targetRun', finalRel⟩ :=
          compile_handle_passthrough cfg stateCfg trace protectedExpr rows source sourceNext target targetNext
            sourceEnv targetEnv _ _ protectedRun targetRun states nextStates (.error (.abort reason)) (by simp)
        have equal := sourceEval.symm.trans sourceRun
        cases equal
        exact ⟨targetFinal, _, targetRun', finalRel, .error (.abort reason)⟩
      | raise valuesRel =>
        rename_i value value'
        let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
        let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
        have fixedStates : StateRel stateCfg sourceFixed targetFixed :=
          stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
        cases rowResult : FlatSem.pmatchRows rows sourceFixed value with
        | typeError =>
          have run := evaluate_handle_rowTypeError trace protectedExpr rows sourceEnv source sourceNext value
            protectedRun rowResult
          rw [sourceEval] at run
          exact (safe (congrArg Prod.snd run)).elim
        | noMatch =>
          obtain ⟨sourceFinal', targetFinal, sourceResult', targetResult', sourceRun, targetRun', finalRel, resultRel⟩ :=
            compile_handle_noMatch_forward cfg stateCfg trace protectedExpr rows source sourceNext target targetNext
              sourceEnv targetEnv value value' protectedRun targetRun fixedStates valuesRel rowResult
          have equal := sourceEval.symm.trans sourceRun
          cases equal
          exact ⟨targetFinal, targetResult', targetRun', finalRel, resultRel⟩
        | «match» selected =>
          rcases selected with ⟨bindings, pattern, body⟩
          have distinct : (FlatLang.patBindings pattern).Nodup := by
            by_cases distinct : (FlatLang.patBindings pattern).Nodup
            · exact distinct
            · have run := evaluate_handle_duplicate trace protectedExpr rows sourceEnv source sourceNext value
                bindings pattern body protectedRun rowResult distinct
              rw [sourceEval] at run
              exact (safe (congrArg Prod.snd run)).elim
          have sourceBody : FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v } sourceFixed [body] =
              (sourceFinal, sourceResult) := by
            have run := evaluate_handle_selected trace protectedExpr rows sourceEnv source sourceNext value
              bindings pattern body protectedRun rowResult distinct
            exact run.symm.trans sourceEval
          have member := pmatchRows_match_mem sourceFixed value rows bindings pattern body rowResult
          have bodySim := bodiesIH pattern body member
          let generated := max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2
          have bodyBound : (compileExp cfg body).1 < generated - 1 := by
            have bodyLe := (compileMatch_member_bound cfg rows pattern body member).1
            dsimp [generated]
            omega
          have bodyIH : ∀ extEnv,
              EnvRel (generated - 1) { sourceEnv with v := bindings ++ sourceEnv.v } extEnv →
              FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v } sourceFixed [body] = (sourceFinal, sourceResult) →
              ∃ targetFinal targetResult,
                FlatSem.evaluate extEnv targetFixed [(compileExp cfg body).2.2] = (targetFinal, targetResult) ∧
                StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
            intro extEnv envRel evaluated
            exact bodySim _ _ _ _ _ _ _ (by dsimp [sourceFixed]; omega) evaluated envRel fixedStates bodyBound safe
          obtain ⟨_, targetFinal, targetResult, targetRun', finalRel, resultRel⟩ :=
            compile_handle_selected_forward cfg stateCfg trace protectedExpr rows source sourceNext target targetNext sourceFinal
              sourceEnv targetEnv value value' bindings pattern body sourceResult n protectedRun targetRun fixedStates
              valuesRel envs (by dsimp [generated] at *; omega) rowResult distinct sourceBody bodyIH
          exact ⟨targetFinal, targetResult, targetRun', finalRel, resultRel⟩

end Flapjack.Compiler.Backend.FlatPattern
