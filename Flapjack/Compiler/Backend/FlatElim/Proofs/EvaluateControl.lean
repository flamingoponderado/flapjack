import Flapjack.Compiler.Backend.FlatElim.Proofs.EvaluateBasic

/-! Control-flow cases of the flat-elimination evaluation simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- A singleton expression list has the same lookup bound as its expression. -/
theorem singletonLookups_within (expression : FlatLang.Exp) (reachable : NumSet)
    (closed : globalsWithin (findLookups expression) reachable) :
    globalsWithin (findGlobalsList destGlobalVarLookup [expression]) reachable := by
  apply (findLookupsList_within_iff _ _).mpr
  intro member inList
  simp only [List.mem_singleton] at inList
  subst member
  exact closed

/-- A single Eval-free expression gives an Eval-free singleton list. -/
theorem singletonExpression_noEval (expression : FlatLang.Exp) (safe : hasEval expression = false) :
    expressionsNoEval [expression] := by
  intro member inList
  simp only [List.mem_singleton] at inList
  subst member
  exact safe

/-- The conditional-expression case of the original evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel_if {C F : Type} (tra : BackendCommon.Tra)
    (cond yes no : FlatLang.Exp)
    (condIH : evaluationSimulation (C := C) (F := F) [cond])
    (yesIH : evaluationSimulation (C := C) (F := F) [yes])
    (noIH : evaluationSimulation (C := C) (F := F) [no]) :
    evaluationSimulation (C := C) (F := F) [.if_ tra cond yes no] := by
  intro env source next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have expressionClosed := (findLookupsList_within_iff _ _).mp lookupsClosed (.if_ tra cond yes no) (by simp)
  simp only [findLookups, findGlobals, globalsWithin_union] at expressionClosed
  have condClosed := singletonLookups_within cond reachable expressionClosed.1
  have yesClosed := singletonLookups_within yes reachable expressionClosed.2.1
  have noClosed := singletonLookups_within no reachable expressionClosed.2.2
  have expressionSafe := expressionsSafe (.if_ tra cond yes no) (by simp)
  simp [hasEval] at expressionSafe
  have condSafe := singletonExpression_noEval cond expressionSafe.1.1
  have yesSafe := singletonExpression_noEval yes expressionSafe.1.2
  have noSafe := singletonExpression_noEval no expressionSafe.2
  cases condEval : FlatSem.evaluate env source [cond] with
  | mk condState condResult =>
    simp only [FlatSem.evaluate, condEval, FlatSem.fixClock] at run
    have condNotTypeError : condResult ≠ .err (.abort .typeError) := by
      intro bad
      subst condResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetCondState, targetCondEval, condRelated, condResultClosed, condResultSafe⟩ :=
      condIH env source condState condResult reachable target condEval condClosed related envClosed envSafe condSafe condNotTypeError
    have clampedRelated := flatStateRel_fixClock reachable source target condState targetCondState condResult related condRelated
    simp only [FlatSem.fixClock] at clampedRelated
    cases condResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ targetCondState with clock := min target.clock targetCondState.clock }, ?_,
        clampedRelated, condResultClosed, condResultSafe⟩
      simp [FlatSem.evaluate, targetCondEval, FlatSem.fixClock]
    | val values =>
      obtain ⟨value, rfl⟩ := Flapjack.Compiler.Backend.FlatProps.evaluate_sing env source condState cond values condEval
      simp only at run
      split at run
      · simp at run
        rcases run with ⟨_, rfl⟩
        exact (notTypeError rfl).elim
      · rename_i branch selected
        have choice := FlatSem.doIf_selected value yes no branch selected
        rcases choice with yesEq | noEq
        · rw [yesEq] at run
          obtain ⟨targetNext, evaluated, nextRelated, closed, safe⟩ :=
            yesIH env _ next result reachable _ run yesClosed clampedRelated envClosed envSafe yesSafe notTypeError
          refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
          rw [FlatSem.evaluate]
          simp only [targetCondEval, FlatSem.fixClock]
          split
          · rename_i noSelection
            rw [selected] at noSelection
            contradiction
          · rename_i targetBranch targetSelection
            have same : targetBranch = branch := Option.some.inj (targetSelection.symm.trans selected)
            subst targetBranch
            simpa [yesEq] using evaluated
        · rw [noEq] at run
          obtain ⟨targetNext, evaluated, nextRelated, closed, safe⟩ :=
            noIH env _ next result reachable _ run noClosed clampedRelated envClosed envSafe noSafe notTypeError
          refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
          rw [FlatSem.evaluate]
          simp only [targetCondEval, FlatSem.fixClock]
          split
          · rename_i noSelection
            rw [selected] at noSelection
            contradiction
          · rename_i targetBranch targetSelection
            have same : targetBranch = branch := Option.some.inj (targetSelection.symm.trans selected)
            subst targetBranch
            simpa [noEq] using evaluated

/-- The local-binding case of the original evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel_let {C F : Type} (tra : BackendCommon.Tra)
    (name : Option Flapjack.AstHOL.VarN) (first body : FlatLang.Exp)
    (firstIH : evaluationSimulation (C := C) (F := F) [first])
    (bodyIH : evaluationSimulation (C := C) (F := F) [body]) :
    evaluationSimulation (C := C) (F := F) [.let_ tra name first body] := by
  intro env source next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have expressionClosed := (findLookupsList_within_iff _ _).mp lookupsClosed (.let_ tra name first body) (by simp)
  simp only [findLookups, findGlobals, globalsWithin_union] at expressionClosed
  have firstClosed := singletonLookups_within first reachable expressionClosed.1
  have bodyClosed := singletonLookups_within body reachable expressionClosed.2
  have expressionSafe := expressionsSafe (.let_ tra name first body) (by simp)
  simp [hasEval] at expressionSafe
  have firstSafe := singletonExpression_noEval first expressionSafe.1
  have bodySafe := singletonExpression_noEval body expressionSafe.2
  cases firstEval : FlatSem.evaluate env source [first] with
  | mk firstState firstResult =>
    simp only [FlatSem.evaluate, firstEval, FlatSem.fixClock] at run
    have firstNotTypeError : firstResult ≠ .err (.abort .typeError) := by
      intro bad
      subst firstResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetFirstState, targetFirstEval, firstRelated, firstResultClosed, firstResultSafe⟩ :=
      firstIH env source firstState firstResult reachable target firstEval firstClosed related envClosed envSafe firstSafe firstNotTypeError
    have clampedRelated := flatStateRel_fixClock reachable source target firstState targetFirstState firstResult related firstRelated
    simp only [FlatSem.fixClock] at clampedRelated
    cases firstResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ targetFirstState with clock := min target.clock targetFirstState.clock }, ?_,
        clampedRelated, firstResultClosed, firstResultSafe⟩
      simp [FlatSem.evaluate, targetFirstEval, FlatSem.fixClock]
    | val values =>
      obtain ⟨value, rfl⟩ := Flapjack.Compiler.Backend.FlatProps.evaluate_sing env source firstState first values firstEval
      have valueClosed : globalsWithin (findValueGlobals value) reachable := by
        have h : globalsWithin (findValuesGlobals [value]) reachable := by
          simpa [findPrimitiveResultGlobals] using firstResultClosed
        exact (findValuesGlobals_within_iff _ _).mp h value (by simp)
      have valueSafe : valueHasEval value = false := by
        have h : valuesNoEval [value] := by
          simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using firstResultSafe
        exact h value (by simp)
      cases name with
      | none =>
        simp only at run
        obtain ⟨targetNext, evaluated, nextRelated, closed, safe⟩ :=
          bodyIH env _ next result reachable _ run bodyClosed clampedRelated envClosed envSafe bodySafe notTypeError
        refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
        simpa [FlatSem.evaluate, targetFirstEval, FlatSem.fixClock] using evaluated
      | some name =>
        simp only at run
        have extendedClosed : globalsWithin (findEnvGlobals { env with v := (name, value) :: env.v }) reachable := by
          exact (bindingsWithin_cons name value env.v reachable).mpr ⟨valueClosed, envClosed⟩
        have extendedSafe : bindingsNoEval ((name, value) :: env.v) := by
          simpa [bindingsNoEval] using And.intro valueSafe envSafe
        obtain ⟨targetNext, evaluated, nextRelated, closed, safe⟩ :=
          bodyIH { env with v := (name, value) :: env.v } _ next result reachable _ run bodyClosed clampedRelated
            extendedClosed extendedSafe bodySafe notTypeError
        refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
        simpa [FlatSem.evaluate, targetFirstEval, FlatSem.fixClock] using evaluated

/-- Building recursive bindings preserves the environment invariants when the
captured environment and all recursive bodies are closed and Eval-free. -/
theorem buildRecEnv_invariants (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (reachable : NumSet)
    (envClosed : globalsWithin (findEnvGlobals env) reachable) (envSafe : bindingsNoEval env.v)
    (funsClosed : globalsWithin (findGlobalsFuns destGlobalVarLookup funs) reachable)
    (funsSafe : hasEvalFuns funs = false) :
    globalsWithin (findEnvGlobals { env with v := FlatSem.buildRecEnv funs env env.v }) reachable ∧
      bindingsNoEval (FlatSem.buildRecEnv funs env env.v) := by
  have envValuesSafe : valuesNoEval (env.v.map Prod.snd) := by
    intro value member
    obtain ⟨binding, bindingMember, eq⟩ := List.mem_map.mp member
    subst value
    exact envSafe binding bindingMember
  have envBindingsSafe : bindingsHaveEval env.v = false := by
    rw [bindingsHaveEval_eq_map]
    exact (valuesHaveEval_eq_false_iff _).mpr envValuesSafe
  have recClosed (name : Flapjack.AstHOL.VarN) :
      globalsWithin (findValueGlobals (.recclosure env funs name)) reachable := by
    cases env with
    | mk bindings =>
      simp only [findValueGlobals, findBindingsGlobals_eq_map, globalsWithin_union]
      exact ⟨envClosed, funsClosed⟩
  have recSafe (name : Flapjack.AstHOL.VarN) : valueHasEval (.recclosure env funs name) = false := by
    cases env with
    | mk bindings => simp [valueHasEval, envBindingsSafe, funsSafe]
  have foldInvariant (todo : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
      bindingsWithin (todo.foldr (fun (f, _, _) acc => (f, .recclosure env funs f) :: acc) env.v) reachable ∧
      bindingsNoEval (todo.foldr (fun (f, _, _) acc => (f, .recclosure env funs f) :: acc) env.v) := by
    induction todo with
    | nil => exact ⟨envClosed, envSafe⟩
    | cons entry rest ih =>
      obtain ⟨f, arg, body⟩ := entry
      simp only [List.foldr_cons]
      constructor
      · exact (bindingsWithin_cons f (.recclosure env funs f) _ reachable).mpr ⟨recClosed f, ih.1⟩
      · simpa [bindingsNoEval] using And.intro (recSafe f) ih.2
  exact foldInvariant funs

/-- The recursive-binding case of the original evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel_letrec {C F : Type} (name : Flapjack.AstHOL.VarN)
    (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) (body : FlatLang.Exp)
    (bodyIH : evaluationSimulation (C := C) (F := F) [body]) :
    evaluationSimulation (C := C) (F := F) [.letrec name funs body] := by
  intro env source next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have expressionClosed := (findLookupsList_within_iff _ _).mp lookupsClosed (.letrec name funs body) (by simp)
  simp only [findLookups, findGlobals, globalsWithin_union] at expressionClosed
  have bodyClosed := singletonLookups_within body reachable expressionClosed.2
  have expressionSafe := expressionsSafe (.letrec name funs body) (by simp)
  simp [hasEval] at expressionSafe
  have bodySafe := singletonExpression_noEval body expressionSafe.1
  have extended := buildRecEnv_invariants funs env reachable envClosed envSafe expressionClosed.1 expressionSafe.2
  by_cases distinct : (funs.map Prod.fst).Nodup
  · simp [FlatSem.evaluate, distinct] at run
    obtain ⟨targetNext, evaluated, nextRelated, closed, safe⟩ :=
      bodyIH { env with v := FlatSem.buildRecEnv funs env env.v } source next result reachable target
        run bodyClosed related extended.1 extended.2 bodySafe notTypeError
    exact ⟨targetNext, by simpa [FlatSem.evaluate, distinct] using evaluated, nextRelated, closed, safe⟩
  · simp [FlatSem.evaluate, distinct] at run
    rcases run with ⟨_, rfl⟩
    exact (notTypeError rfl).elim

/-- Related states select the same pattern row. -/
theorem selectRow_related {C F : Type} (reachable : NumSet) (source target : FlatSem.State C F)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (value noMatch : FlatSem.Value)
    (related : flatStateRel reachable source target) :
    FlatSem.selectRow target rows value noMatch = FlatSem.selectRow source rows value noMatch := by
  simp [FlatSem.selectRow, flatStateRel_pmatchRows reachable source target rows value related]

/-- Successful row selection identifies the matching pattern and row. -/
theorem selectRow_success {C F : Type} (state : FlatSem.State C F)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (value noMatch : FlatSem.Value)
    (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value)) (body : FlatLang.Exp)
    (selected : FlatSem.selectRow state rows value noMatch = .ok (bindings, body)) :
    ∃ pattern, FlatSem.pmatchRows rows state value = .match (bindings, pattern, body) := by
  cases matched : FlatSem.pmatchRows rows state value with
  | typeError => simp [FlatSem.selectRow, matched] at selected
  | noMatch => simp [FlatSem.selectRow, matched] at selected
  | «match» row =>
    obtain ⟨rowBindings, pattern, expression⟩ := row
    by_cases distinct : (FlatLang.patBindings pattern).Nodup
    · simp [FlatSem.selectRow, matched, distinct] at selected
      rcases selected with ⟨rfl, rfl⟩
      exact ⟨pattern, rfl⟩
    · simp [FlatSem.selectRow, matched, distinct] at selected

/-- A row body contributes its lookups to the pattern-row analysis. -/
theorem findGlobalsPats_member (rows : List (FlatLang.Pat × FlatLang.Exp))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp) (member : (pattern, body) ∈ rows)
    (key : Nat) (found : sptMem key (findLookups body)) :
    sptMem key (findGlobalsPats destGlobalVarLookup rows) := by
  induction rows with
  | nil => simp at member
  | cons row rest ih =>
    obtain ⟨p, e⟩ := row
    simp only [List.mem_cons] at member
    simp only [findGlobalsPats, sptMem_sptUnion]
    rcases member with same | member
    · cases same
      exact Or.inl found
    · exact Or.inr (ih member)

/-- An Eval-free pattern-row analysis makes each row body Eval-free. -/
theorem hasEvalPats_member (rows : List (FlatLang.Pat × FlatLang.Exp))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp) (member : (pattern, body) ∈ rows)
    (safe : hasEvalPats rows = false) : hasEval body = false := by
  induction rows with
  | nil => simp at member
  | cons row rest ih =>
    obtain ⟨p, e⟩ := row
    simp only [List.mem_cons] at member
    simp [hasEvalPats] at safe
    rcases member with same | member
    · cases same
      exact safe.1
    · exact ih member safe.2

/-- Appending two closed pattern environments preserves the global bound. -/
theorem bindingsWithin_append (left right : List (Flapjack.AstHOL.VarN × FlatSem.Value))
    (reachable : NumSet) (leftClosed : bindingsWithin left reachable) (rightClosed : bindingsWithin right reachable) :
    bindingsWithin (left ++ right) reachable := by
  apply (findValuesGlobals_within_iff _ _).mpr
  intro value member
  simp only [List.map_append, List.mem_append] at member
  rcases member with leftMember | rightMember
  · exact (findValuesGlobals_within_iff _ _).mp leftClosed value leftMember
  · exact (findValuesGlobals_within_iff _ _).mp rightClosed value rightMember

/-- Appending two Eval-free pattern environments preserves that invariant. -/
theorem bindingsNoEval_append (left right : List (Flapjack.AstHOL.VarN × FlatSem.Value))
    (leftSafe : bindingsNoEval left) (rightSafe : bindingsNoEval right) : bindingsNoEval (left ++ right) := by
  intro binding member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact leftSafe binding leftMember
  · exact rightSafe binding rightMember

/-- A selected row and its environment satisfy the invariants required to
apply the branch induction hypothesis. -/
theorem selectRow_invariants {C F : Type} (reachable : NumSet) (state : FlatSem.State C F)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (value noMatch : FlatSem.Value)
    (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value)) (body : FlatLang.Exp)
    (selected : FlatSem.selectRow state rows value noMatch = .ok (bindings, body))
    (rowsClosed : globalsWithin (findGlobalsPats destGlobalVarLookup rows) reachable)
    (rowsSafe : hasEvalPats rows = false)
    (valueClosed : globalsWithin (findValueGlobals value) reachable) (valueSafe : valueHasEval value = false)
    (refsClosed : globalsWithin (findRefsGlobals state.refs) reachable) (refsSafe : storeHasNoEval state.refs) :
    globalsWithin (findLookups body) reachable ∧ hasEval body = false ∧
      bindingsWithin bindings reachable ∧ bindingsNoEval bindings := by
  obtain ⟨pattern, matched⟩ := selectRow_success state rows value noMatch bindings body selected
  have member := pmatchRows_selected_mem rows state value bindings pattern body matched
  have bindingInvariants := pmatchRows_selected_invariants rows state value bindings pattern body reachable
    matched valueSafe refsSafe valueClosed refsClosed
  refine ⟨?_, hasEvalPats_member rows pattern body member rowsSafe, bindingInvariants.2, bindingInvariants.1⟩
  intro key found
  exact rowsClosed key (findGlobalsPats_member rows pattern body member key found)

/-- Row selection can fail only with a type error or the supplied no-match
exception. -/
theorem selectRow_error {C F : Type} (state : FlatSem.State C F)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (value noMatch : FlatSem.Value) (error : ErrorResult FlatSem.Value)
    (selected : FlatSem.selectRow state rows value noMatch = .error error) :
    error = .abort .typeError ∨ error = .raise noMatch := by
  cases matched : FlatSem.pmatchRows rows state value with
  | typeError => simp [FlatSem.selectRow, matched] at selected; exact Or.inl selected.symm
  | noMatch => simp [FlatSem.selectRow, matched] at selected; exact Or.inr selected.symm
  | «match» row =>
    obtain ⟨bindings, pattern, body⟩ := row
    by_cases distinct : (FlatLang.patBindings pattern).Nodup
    · simp [FlatSem.selectRow, matched, distinct] at selected
    · simp [FlatSem.selectRow, matched, distinct] at selected
      exact Or.inl selected.symm

/-- A successfully selected row can be simulated using the induction
hypothesis for the selected source row. -/
theorem evaluate_selectedRow {C F : Type} (rows : List (FlatLang.Pat × FlatLang.Exp))
    (rowIH : ∀ pattern body, (pattern, body) ∈ rows → evaluationSimulation (C := C) (F := F) [body])
    (env : FlatSem.Environment FlatSem.Value) (source target next : FlatSem.State C F)
    (reachable : NumSet) (value noMatch : FlatSem.Value)
    (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value)) (body : FlatLang.Exp)
    (result : Result (List FlatSem.Value) FlatSem.Value)
    (selected : FlatSem.selectRow source rows value noMatch = .ok (bindings, body))
    (run : FlatSem.evaluate { env with v := bindings ++ env.v } source [body] = (next, result))
    (related : flatStateRel reachable source target)
    (rowsClosed : globalsWithin (findGlobalsPats destGlobalVarLookup rows) reachable)
    (rowsSafe : hasEvalPats rows = false)
    (valueClosed : globalsWithin (findValueGlobals value) reachable) (valueSafe : valueHasEval value = false)
    (envClosed : globalsWithin (findEnvGlobals env) reachable) (envSafe : bindingsNoEval env.v)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, FlatSem.evaluate { env with v := bindings ++ env.v } target [body] = (targetNext, result) ∧
      flatStateRel reachable next targetNext ∧ globalsWithin (findPrimitiveResultGlobals result) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues result) := by
  obtain ⟨pattern, matched⟩ := selectRow_success source rows value noMatch bindings body selected
  have member := pmatchRows_selected_mem rows source value bindings pattern body matched
  have invariants := selectRow_invariants reachable source rows value noMatch bindings body selected
    rowsClosed rowsSafe valueClosed valueSafe related.2.2.2.2.1 related.2.2.2.2.2
  exact rowIH pattern body member { env with v := bindings ++ env.v } source next result reachable target run
    (singletonLookups_within body reachable invariants.1) related
    (bindingsWithin_append bindings env.v reachable invariants.2.2.1 envClosed)
    (bindingsNoEval_append bindings env.v invariants.2.2.2 envSafe)
    (singletonExpression_noEval body invariants.2.1) notTypeError

/-- The pattern-match case of the original evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel_mat {C F : Type} (tra : BackendCommon.Tra)
    (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (bodyIH : evaluationSimulation (C := C) (F := F) [body])
    (rowIH : ∀ pattern branch, (pattern, branch) ∈ rows → evaluationSimulation (C := C) (F := F) [branch]) :
    evaluationSimulation (C := C) (F := F) [.mat tra body rows] := by
  intro env source next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have expressionClosed := (findLookupsList_within_iff _ _).mp lookupsClosed (.mat tra body rows) (by simp)
  simp only [findLookups, findGlobals, globalsWithin_union] at expressionClosed
  have bodyClosed := singletonLookups_within body reachable expressionClosed.1
  have expressionSafe := expressionsSafe (.mat tra body rows) (by simp)
  simp [hasEval] at expressionSafe
  have bodySafe := singletonExpression_noEval body expressionSafe.1
  cases bodyEval : FlatSem.evaluate env source [body] with
  | mk bodyState bodyResult =>
    simp only [FlatSem.evaluate, bodyEval, FlatSem.fixClock] at run
    have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetBodyState, targetBodyEval, bodyRelated, bodyResultClosed, bodyResultSafe⟩ :=
      bodyIH env source bodyState bodyResult reachable target bodyEval bodyClosed related envClosed envSafe bodySafe bodyNotTypeError
    have clampedRelated := flatStateRel_fixClock reachable source target bodyState targetBodyState bodyResult related bodyRelated
    simp only [FlatSem.fixClock] at clampedRelated
    cases bodyResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ targetBodyState with clock := min target.clock targetBodyState.clock }, ?_,
        clampedRelated, bodyResultClosed, bodyResultSafe⟩
      simp [FlatSem.evaluate, targetBodyEval, FlatSem.fixClock]
    | val values =>
      obtain ⟨value, rfl⟩ := Flapjack.Compiler.Backend.FlatProps.evaluate_sing env source bodyState body values bodyEval
      have valueClosed : globalsWithin (findValueGlobals value) reachable := by
        have h : globalsWithin (findValuesGlobals [value]) reachable := by
          simpa [findPrimitiveResultGlobals] using bodyResultClosed
        exact (findValuesGlobals_within_iff _ _).mp h value (by simp)
      have valueSafe : valueHasEval value = false := by
        have h : valuesNoEval [value] := by
          simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using bodyResultSafe
        exact h value (by simp)
      simp only at run
      split at run
      · rename_i error selected
        simp only [bodyEval] at selected
        change FlatSem.selectRow { bodyState with clock := min source.clock bodyState.clock } rows value FlatSem.bindExnV = .error error at selected
        have shape := selectRow_error _ rows value FlatSem.bindExnV error selected
        rcases shape with bad | raised
        · subst error
          simp at run
          rcases run with ⟨_, rfl⟩
          exact (notTypeError rfl).elim
        · subst error
          rcases run with ⟨rfl, rfl⟩
          have bindClosed : globalsWithin (findValueGlobals FlatSem.bindExnV) reachable := by
            simp [FlatSem.bindExnV, findValueGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain]
          have bindSafe : valueHasEval FlatSem.bindExnV = false := by simp [FlatSem.bindExnV, valueHasEval, valuesHaveEval]
          have resultSafe := primitiveResult_raise_invariants reachable FlatSem.bindExnV bindClosed bindSafe
          refine ⟨{ targetBodyState with clock := min target.clock targetBodyState.clock }, ?_, clampedRelated, resultSafe.1, resultSafe.2⟩
          rw [FlatSem.evaluate]
          simp only [targetBodyEval, FlatSem.fixClock]
          split
          · rename_i targetError targetSelected
            simp only [targetBodyEval] at targetSelected
            change FlatSem.selectRow { targetBodyState with clock := min target.clock targetBodyState.clock } rows value FlatSem.bindExnV = .error targetError at targetSelected
            have sameSelection := selectRow_related reachable _ _ rows value FlatSem.bindExnV clampedRelated
            have same : targetError = .raise FlatSem.bindExnV := Except.error.inj (targetSelected.symm.trans (sameSelection.trans selected))
            subst targetError
            rfl
          · rename_i targetBindings targetBranch targetSelected
            simp only [targetBodyEval] at targetSelected
            change FlatSem.selectRow { targetBodyState with clock := min target.clock targetBodyState.clock } rows value FlatSem.bindExnV = .ok (targetBindings, targetBranch) at targetSelected
            have sameSelection := selectRow_related reachable _ _ rows value FlatSem.bindExnV clampedRelated
            have impossible := targetSelected.symm.trans (sameSelection.trans selected)
            cases impossible
      · rename_i bindings branch selected
        simp only [bodyEval] at selected
        change FlatSem.selectRow { bodyState with clock := min source.clock bodyState.clock } rows value FlatSem.bindExnV = .ok (bindings, branch) at selected
        obtain ⟨targetNext, evaluated, nextRelated, closed, safe⟩ :=
          evaluate_selectedRow rows rowIH env _ _ next reachable value FlatSem.bindExnV bindings branch result
            selected run clampedRelated expressionClosed.2 expressionSafe.2 valueClosed valueSafe envClosed envSafe notTypeError
        refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
        rw [FlatSem.evaluate]
        simp only [targetBodyEval, FlatSem.fixClock]
        split
        · rename_i targetError targetSelected
          simp only [targetBodyEval] at targetSelected
          change FlatSem.selectRow { targetBodyState with clock := min target.clock targetBodyState.clock } rows value FlatSem.bindExnV = .error targetError at targetSelected
          have sameSelection := selectRow_related reachable _ _ rows value FlatSem.bindExnV clampedRelated
          have impossible := targetSelected.symm.trans (sameSelection.trans selected)
          cases impossible
        · rename_i targetBindings targetBranch targetSelected
          simp only [targetBodyEval] at targetSelected
          change FlatSem.selectRow { targetBodyState with clock := min target.clock targetBodyState.clock } rows value FlatSem.bindExnV = .ok (targetBindings, targetBranch) at targetSelected
          have sameSelection := selectRow_related reachable _ _ rows value FlatSem.bindExnV clampedRelated
          have same : (targetBindings, targetBranch) = (bindings, branch) := Except.ok.inj (targetSelected.symm.trans (sameSelection.trans selected))
          cases same
          exact evaluated

end Flapjack.Compiler.Backend.FlatElim
