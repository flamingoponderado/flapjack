import Flapjack.Compiler.Backend.FlatElim.Proofs.PureApplication

/-! Control-flow induction steps for pure flat evaluation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- A pure singleton has the list purity property. -/
theorem singletonPure (expression : FlatLang.Exp) (pure : isPure expression = true) :
    ∀ member ∈ [expression], isPure member = true := by
  intro member belongs
  simp only [List.mem_singleton] at belongs
  subst member
  exact pure

/-- A singleton's location-disjointness gives the list property. -/
theorem singletonLocations (expression : FlatLang.Exp) (reachable : NumSet)
    (empty : sptIsEmpty (sptInter (findLoc expression) reachable) = true) :
    ∀ member ∈ [expression], sptIsEmpty (sptInter (findLoc member) reachable) = true := by
  intro member belongs
  simp only [List.mem_singleton] at belongs
  subst member
  exact empty

/-- Pure local binding preserves the unchanged target state. -/
theorem pureEvaluation_let {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (name : Option Flapjack.AstHOL.VarN)
    (first body : FlatLang.Exp) (firstIH : pureEvaluationSimulationAt env source [first])
    (bodyIH : ∀ newEnv (newState : FlatSem.State C F), newState.clock ≤ source.clock →
      pureEvaluationSimulationAt newEnv newState [body]) :
    pureEvaluationSimulationAt env source [.let_ tra name first body] := by
  intro next result reachable target run expressionsPure envSafe expressionsSafe locationsEmpty related notTypeError
  have pure := expressionsPure (.let_ tra name first body) (by simp)
  simp [isPure] at pure
  have safe := expressionsSafe (.let_ tra name first body) (by simp)
  simp [hasEval] at safe
  have empty := locationsEmpty (.let_ tra name first body) (by simp)
  simp only [findLoc, findGlobals] at empty
  have disjoint := interEmpty_union _ _ reachable empty
  cases firstEval : FlatSem.evaluate env source [first] with
  | mk firstState firstResult =>
    simp only [FlatSem.evaluate, firstEval, FlatSem.fixClock] at run
    have firstNotTypeError : firstResult ≠ .err (.abort .typeError) := by
      intro bad
      subst firstResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨values, firstRelated, resultEq, valuesSafe⟩ :=
      firstIH firstState firstResult reachable target firstEval (singletonPure first pure.1) envSafe
        (singletonExpression_noEval first safe.1) (singletonLocations first reachable disjoint.1) related firstNotTypeError
    subst firstResult
    obtain ⟨value, rfl⟩ := Flapjack.Compiler.Backend.FlatProps.evaluate_sing env source firstState first values firstEval
    have valueSafe : valueHasEval value = false := valuesSafe value (by simp)
    have clocks : source.clock = firstState.clock := related.1.trans firstRelated.1.symm
    simp only [clocks, Nat.min_self] at run
    cases name with
    | none =>
      simp only at run
      exact bodyIH env firstState (by omega) next result reachable target run (singletonPure body pure.2)
        envSafe (singletonExpression_noEval body safe.2) (singletonLocations body reachable disjoint.2) firstRelated notTypeError
    | some name =>
      simp only at run
      have extendedSafe : bindingsNoEval ((name, value) :: env.v) := by
        simpa [bindingsNoEval] using And.intro valueSafe envSafe
      exact bodyIH { env with v := (name, value) :: env.v } firstState (by omega) next result reachable target run
        (singletonPure body pure.2) extendedSafe (singletonExpression_noEval body safe.2)
        (singletonLocations body reachable disjoint.2) firstRelated notTypeError

/-- Pure conditional evaluation preserves the unchanged target state. -/
theorem pureEvaluation_if {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (cond yes no : FlatLang.Exp)
    (condIH : pureEvaluationSimulationAt env source [cond])
    (yesIH : ∀ newState : FlatSem.State C F, newState.clock ≤ source.clock → pureEvaluationSimulationAt env newState [yes])
    (noIH : ∀ newState : FlatSem.State C F, newState.clock ≤ source.clock → pureEvaluationSimulationAt env newState [no]) :
    pureEvaluationSimulationAt env source [.if_ tra cond yes no] := by
  intro next result reachable target run expressionsPure envSafe expressionsSafe locationsEmpty related notTypeError
  have pure := expressionsPure (.if_ tra cond yes no) (by simp)
  simp [isPure] at pure
  have safe := expressionsSafe (.if_ tra cond yes no) (by simp)
  simp [hasEval] at safe
  have empty := locationsEmpty (.if_ tra cond yes no) (by simp)
  simp only [findLoc, findGlobals] at empty
  have outer := interEmpty_union _ _ reachable empty
  have inner := interEmpty_union _ _ reachable outer.2
  cases condEval : FlatSem.evaluate env source [cond] with
  | mk condState condResult =>
    simp only [FlatSem.evaluate, condEval, FlatSem.fixClock] at run
    have condNotTypeError : condResult ≠ .err (.abort .typeError) := by
      intro bad
      subst condResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨values, condRelated, resultEq, _⟩ :=
      condIH condState condResult reachable target condEval (singletonPure cond pure.1.1) envSafe
        (singletonExpression_noEval cond safe.1.1) (singletonLocations cond reachable outer.1) related condNotTypeError
    subst condResult
    obtain ⟨value, rfl⟩ := Flapjack.Compiler.Backend.FlatProps.evaluate_sing env source condState cond values condEval
    have clocks : source.clock = condState.clock := related.1.trans condRelated.1.symm
    simp only [clocks, Nat.min_self] at run
    split at run
    · simp at run
      rcases run with ⟨_, rfl⟩
      exact (notTypeError rfl).elim
    · rename_i branch selected
      have choice := FlatSem.doIf_selected value yes no branch selected
      rcases choice with yesEq | noEq
      · rw [yesEq] at run
        exact yesIH condState (by omega) next result reachable target run (singletonPure yes pure.1.2)
          envSafe (singletonExpression_noEval yes safe.1.2) (singletonLocations yes reachable inner.1) condRelated notTypeError
      · rw [noEq] at run
        exact noIH condState (by omega) next result reachable target run (singletonPure no pure.2)
          envSafe (singletonExpression_noEval no safe.2) (singletonLocations no reachable inner.2) condRelated notTypeError

/-- A pure handler cannot enter a handler row because its protected body
cannot produce an exception under the pure-evaluation induction hypothesis. -/
theorem pureEvaluation_handle {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (body : FlatLang.Exp)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (bodyIH : pureEvaluationSimulationAt env source [body]) :
    pureEvaluationSimulationAt env source [.handle tra body rows] := by
  intro next result reachable target run expressionsPure envSafe expressionsSafe locationsEmpty related notTypeError
  have pure := expressionsPure (.handle tra body rows) (by simp)
  have bodyPure : isPure body = true := by simpa [isPure] using pure
  have safe := expressionsSafe (.handle tra body rows) (by simp)
  simp [hasEval] at safe
  have empty := locationsEmpty (.handle tra body rows) (by simp)
  simp only [findLoc, findGlobals] at empty
  have disjoint := interEmpty_union _ _ reachable empty
  cases bodyEval : FlatSem.evaluate env source [body] with
  | mk bodyState bodyResult =>
    simp only [FlatSem.evaluate, bodyEval, FlatSem.fixClock] at run
    have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨values, bodyRelated, resultEq, valuesSafe⟩ :=
      bodyIH bodyState bodyResult reachable target bodyEval (singletonPure body bodyPure) envSafe
        (singletonExpression_noEval body safe.1) (singletonLocations body reachable disjoint.1) related bodyNotTypeError
    subst bodyResult
    have clocks : source.clock = bodyState.clock := related.1.trans bodyRelated.1.symm
    simp [clocks] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨values, bodyRelated, rfl, valuesSafe⟩

/-- Building a recursive environment preserves Eval-freedom when both its
captured environment and recursive bodies are Eval-free. -/
theorem buildRecEnv_noEval (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (envSafe : bindingsNoEval env.v) (funsSafe : hasEvalFuns funs = false) :
    bindingsNoEval (FlatSem.buildRecEnv funs env env.v) := by
  have envValuesSafe : valuesNoEval (env.v.map Prod.snd) := by
    intro value member
    obtain ⟨binding, bindingMember, eq⟩ := List.mem_map.mp member
    subst value
    exact envSafe binding bindingMember
  have envBindingsSafe : bindingsHaveEval env.v = false := by
    rw [bindingsHaveEval_eq_map]
    exact (valuesHaveEval_eq_false_iff _).mpr envValuesSafe
  have recSafe (name : Flapjack.AstHOL.VarN) : valueHasEval (.recclosure env funs name) = false := by
    cases env with
    | mk bindings => simp [valueHasEval, envBindingsSafe, funsSafe]
  have foldSafe (todo : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
      bindingsNoEval (todo.foldr (fun (f, _, _) acc => (f, .recclosure env funs f) :: acc) env.v) := by
    induction todo with
    | nil => exact envSafe
    | cons entry rest ih =>
      obtain ⟨f, arg, body⟩ := entry
      simpa [bindingsNoEval] using And.intro (recSafe f) ih
  exact foldSafe funs

/-- Pure recursive binding preserves the unchanged target state. -/
theorem pureEvaluation_letrec {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (name : Flapjack.AstHOL.VarN)
    (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) (body : FlatLang.Exp)
    (bodyIH : ∀ newEnv, pureEvaluationSimulationAt newEnv source [body]) :
    pureEvaluationSimulationAt env source [.letrec name funs body] := by
  intro next result reachable target run expressionsPure envSafe expressionsSafe locationsEmpty related notTypeError
  have pure := expressionsPure (.letrec name funs body) (by simp)
  have bodyPure : isPure body = true := by simpa [isPure] using pure
  have safe := expressionsSafe (.letrec name funs body) (by simp)
  simp [hasEval] at safe
  have empty := locationsEmpty (.letrec name funs body) (by simp)
  simp only [findLoc, findGlobals] at empty
  have disjoint := interEmpty_union _ _ reachable empty
  by_cases distinct : (funs.map Prod.fst).Nodup
  · simp [FlatSem.evaluate, distinct] at run
    exact bodyIH { env with v := FlatSem.buildRecEnv funs env env.v } next result reachable target run
      (singletonPure body bodyPure) (buildRecEnv_noEval funs env envSafe safe.2)
      (singletonExpression_noEval body safe.1) (singletonLocations body reachable disjoint.2) related notTypeError
  · simp [FlatSem.evaluate, distinct] at run
    rcases run with ⟨_, rfl⟩
    exact (notTypeError rfl).elim

/-- Every row body of a pure pattern match is pure. -/
theorem allPureBranches_member (rows : List (FlatLang.Pat × FlatLang.Exp)) (pattern : FlatLang.Pat)
    (body : FlatLang.Exp) (member : (pattern, body) ∈ rows) (pure : allPureBranches rows = true) :
    isPure body = true := by
  induction rows with
  | nil => simp at member
  | cons row rest ih =>
    obtain ⟨p, e⟩ := row
    simp [allPureBranches] at pure
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact pure.1
    · exact ih member pure.2

/-- Each row body's locations occur in the row-list analysis. -/
theorem findLocPats_member (rows : List (FlatLang.Pat × FlatLang.Exp)) (pattern : FlatLang.Pat)
    (body : FlatLang.Exp) (member : (pattern, body) ∈ rows) (key : Nat) (found : sptMem key (findLoc body)) :
    sptMem key (findGlobalsPats destGlobalVarInit rows) := by
  induction rows with
  | nil => simp at member
  | cons row rest ih =>
    obtain ⟨p, e⟩ := row
    simp only [findGlobalsPats, sptMem_sptUnion]
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact Or.inl found
    · exact Or.inr (ih member)

/-- The expression-row total-pattern analysis agrees with the polymorphic
row predicate used by the matching theorem. -/
theorem hasTotalPat_eq_any (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    hasTotalPat rows = rows.any (fun row => totalPat row.1) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨pattern, body⟩ := row
    simp only [hasTotalPat, List.any_cons, ih]

/-- A selected row can raise its no-match exception only if row matching
actually returned no-match. -/
theorem selectRow_raise_noMatch {C F : Type} (state : FlatSem.State C F)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (value noMatch : FlatSem.Value)
    (selected : FlatSem.selectRow state rows value noMatch = .error (.raise noMatch)) :
    FlatSem.pmatchRows rows state value = .noMatch := by
  cases matched : FlatSem.pmatchRows rows state value with
  | typeError => simp [FlatSem.selectRow, matched] at selected
  | noMatch => rfl
  | «match» row =>
    obtain ⟨bindings, pattern, body⟩ := row
    by_cases distinct : (FlatLang.patBindings pattern).Nodup <;> simp [FlatSem.selectRow, matched, distinct] at selected

/-- Pure pattern matching preserves the unchanged target state. -/
theorem pureEvaluation_mat {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (body : FlatLang.Exp)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (bodyIH : pureEvaluationSimulationAt env source [body])
    (rowIH : ∀ pattern branch, (pattern, branch) ∈ rows → ∀ newEnv (newState : FlatSem.State C F),
      newState.clock ≤ source.clock → pureEvaluationSimulationAt newEnv newState [branch]) :
    pureEvaluationSimulationAt env source [.mat tra body rows] := by
  intro next result reachable target run expressionsPure envSafe expressionsSafe locationsEmpty related notTypeError
  have pure := expressionsPure (.mat tra body rows) (by simp)
  simp [isPure] at pure
  have safe := expressionsSafe (.mat tra body rows) (by simp)
  simp [hasEval] at safe
  have empty := locationsEmpty (.mat tra body rows) (by simp)
  simp only [findLoc, findGlobals] at empty
  have disjoint := interEmpty_union _ _ reachable empty
  cases bodyEval : FlatSem.evaluate env source [body] with
  | mk bodyState bodyResult =>
    simp only [FlatSem.evaluate, bodyEval, FlatSem.fixClock] at run
    have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨values, bodyRelated, resultEq, valuesSafe⟩ :=
      bodyIH bodyState bodyResult reachable target bodyEval (singletonPure body pure.1.1) envSafe
        (singletonExpression_noEval body safe.1) (singletonLocations body reachable disjoint.1) related bodyNotTypeError
    subst bodyResult
    obtain ⟨value, rfl⟩ := Flapjack.Compiler.Backend.FlatProps.evaluate_sing env source bodyState body values bodyEval
    have valueSafe : valueHasEval value = false := valuesSafe value (by simp)
    have clocks : source.clock = bodyState.clock := related.1.trans bodyRelated.1.symm
    simp only [clocks, Nat.min_self] at run
    split at run
    · rename_i error selected
      simp only [bodyEval, clocks, Nat.min_self] at selected
      change FlatSem.selectRow bodyState rows value FlatSem.bindExnV = .error error at selected
      rcases selectRow_error bodyState rows value FlatSem.bindExnV error selected with bad | raised
      · subst error
        simp at run
        rcases run with ⟨_, rfl⟩
        exact (notTypeError rfl).elim
      · subst error
        have noMatch := selectRow_raise_noMatch bodyState rows value FlatSem.bindExnV selected
        have rowTotal : rows.any (fun row => totalPat row.1) = true := by
          rw [← hasTotalPat_eq_any]
          exact pure.2
        exact (exists_totalPat rows bodyState value rowTotal noMatch).elim
    · rename_i bindings branch selected
      simp only [bodyEval, clocks, Nat.min_self] at selected
      change FlatSem.selectRow bodyState rows value FlatSem.bindExnV = .ok (bindings, branch) at selected
      obtain ⟨pattern, matched⟩ := selectRow_success bodyState rows value FlatSem.bindExnV bindings branch selected
      have member := pmatchRows_selected_mem rows bodyState value bindings pattern branch matched
      have patternMatch := pmatchRows_selected_match rows bodyState value bindings pattern branch matched
      have bindingSafe := pmatch_not_has_Eval.1 bodyState pattern value [] bindings patternMatch valueSafe
        bodyRelated.2.2.2.2.2 (by simp [bindingsNoEval])
      have branchSafe := hasEvalPats_member rows pattern branch member safe.2
      have branchPure := allPureBranches_member rows pattern branch member pure.1.2
      have branchEmpty : sptIsEmpty (sptInter (findLoc branch) reachable) = true := by
        apply (interEmpty_iff_disjoint _ _).mpr
        intro key found reach
        exact (interEmpty_iff_disjoint _ _).mp disjoint.2 key (findLocPats_member rows pattern branch member key found) reach
      have extendedSafe := bindingsNoEval_append bindings env.v bindingSafe envSafe
      exact rowIH pattern branch member { env with v := bindings ++ env.v } bodyState (by omega)
        next result reachable target run (singletonPure branch branchPure) extendedSafe
        (singletonExpression_noEval branch branchSafe) (singletonLocations branch reachable branchEmpty) bodyRelated notTypeError

end Flapjack.Compiler.Backend.FlatElim
