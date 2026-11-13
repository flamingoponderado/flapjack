module

public import Flapjack.SemanticPrimitivesProps.RecursiveFunctions
public import Flapjack.Compiler.Backend.FlatElim.Proofs.EvaluateBasic

@[expose] public section

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
  obtain ⟨patternMatch, member⟩ :=
    FlatProps.pmatchRows_imp_pmatch rows state value bindings pattern body matched
  have mapped : findGlobalsPats destGlobalVarLookup rows =
      findGlobalsList destGlobalVarLookup (rows.map Prod.snd) := by
    clear matched selected member rowsClosed rowsSafe
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      obtain ⟨_, _⟩ := row
      simp only [List.map_cons, findGlobalsPats, findGlobalsList, ih]
  exact ⟨pmatchRows_findLookups rows state value bindings pattern body reachable
      ⟨matched, mapped ▸ rowsClosed⟩,
    hasEvalPats_member rows pattern body member rowsSafe,
    pmatch_Match_reachable.1 state pattern value [] bindings reachable
      ⟨patternMatch, valueClosed,
        by simp [bindingsWithin, globalsWithin, findValuesGlobals, sptMem, sptDomain], refsClosed⟩,
    pmatch_not_has_Eval.1 state pattern value [] bindings
      ⟨patternMatch, valueSafe, refsSafe, by simp [bindingsNoEval]⟩⟩

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

/-- Applying an ordinary closure preserves the bounds on the selected body
and the extended environment. -/
theorem closureApplication_invariants (env : FlatSem.Environment FlatSem.Value)
    (name : Flapjack.AstHOL.VarN) (body : FlatLang.Exp) (value : FlatSem.Value) (reachable : NumSet)
    (closureClosed : globalsWithin (findValueGlobals (.closure env name body)) reachable)
    (closureSafe : valueHasEval (.closure env name body) = false)
    (valueClosed : globalsWithin (findValueGlobals value) reachable) (valueSafe : valueHasEval value = false) :
    globalsWithin (findLookups body) reachable ∧ hasEval body = false ∧
      globalsWithin (findEnvGlobals { env with v := (name, value) :: env.v }) reachable ∧
      bindingsNoEval ((name, value) :: env.v) := by
  cases env with
  | mk bindings =>
    simp only [findValueGlobals, findBindingsGlobals_eq_map, globalsWithin_union] at closureClosed
    simp [valueHasEval] at closureSafe
    have envSafe : bindingsNoEval bindings := by
      have valuesSafe := (valuesHaveEval_eq_false_iff _).mp (by simpa [bindingsHaveEval_eq_map] using closureSafe.2)
      intro binding member
      exact valuesSafe binding.2 (List.mem_map.mpr ⟨binding, member, rfl⟩)
    refine ⟨closureClosed.2, closureSafe.1, ?_, ?_⟩
    · exact (bindingsWithin_cons name value bindings reachable).mpr ⟨valueClosed, closureClosed.1⟩
    · simpa [bindingsNoEval] using And.intro valueSafe envSafe

/-- Applying a recursive closure preserves the bounds on the selected body
and the environment rebuilt from the recursive function group. -/
theorem recclosureApplication_invariants (env : FlatSem.Environment FlatSem.Value)
    (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp))
    (name arg : Flapjack.AstHOL.VarN) (body : FlatLang.Exp) (value : FlatSem.Value) (reachable : NumSet)
    (found : findRecFun name funs = some (arg, body))
    (closureClosed : globalsWithin (findValueGlobals (.recclosure env funs name)) reachable)
    (closureSafe : valueHasEval (.recclosure env funs name) = false)
    (valueClosed : globalsWithin (findValueGlobals value) reachable) (valueSafe : valueHasEval value = false) :
    globalsWithin (findLookups body) reachable ∧ hasEval body = false ∧
      globalsWithin (findEnvGlobals { env with v := (arg, value) :: FlatSem.buildRecEnv funs env env.v }) reachable ∧
      bindingsNoEval ((arg, value) :: FlatSem.buildRecEnv funs env env.v) := by
  have member : (name, arg, body) ∈ funs :=
    Flapjack.holALookup_member funs name (arg, body) (by
      rw [← Flapjack.SemanticPrimitivesProps.findRecFun_alookup]
      exact found)
  cases env with
  | mk bindings =>
    simp only [findValueGlobals, findBindingsGlobals_eq_map, globalsWithin_union] at closureClosed
    simp [valueHasEval] at closureSafe
    have envSafe : bindingsNoEval bindings := by
      have valuesSafe := (valuesHaveEval_eq_false_iff _).mp (by simpa [bindingsHaveEval_eq_map] using closureSafe.1)
      intro binding bindingMember
      exact valuesSafe binding.2 (List.mem_map.mpr ⟨binding, bindingMember, rfl⟩)
    have built := buildRecEnv_invariants funs ⟨bindings⟩ reachable closureClosed.1 envSafe closureClosed.2 closureSafe.2
    simp only [findFunctionGlobals_eq_map] at closureClosed
    simp only [hasEvalFuns_eq_map] at closureSafe
    have bodyMember : body ∈ funs.map (fun entry => entry.2.2) :=
      List.mem_map.mpr ⟨(name, arg, body), member, rfl⟩
    refine ⟨(findLookupsList_within_iff _ _).mp closureClosed.2 body bodyMember, ?_, ?_, ?_⟩
    · simpa using (List.any_eq_false.mp closureSafe.2) body bodyMember
    · exact (bindingsWithin_cons arg value _ reachable).mpr ⟨valueClosed, built.1⟩
    · simpa [bindingsNoEval] using And.intro valueSafe built.2

/-- Successful function application yields a closed, Eval-free body and
environment whenever its argument values have those invariants. -/
theorem doOpApp_invariants (values : List FlatSem.Value) (env : FlatSem.Environment FlatSem.Value)
    (body : FlatLang.Exp) (reachable : NumSet) (selected : FlatSem.doOpApp values = some (env, body))
    (closed : globalsWithin (findValuesGlobals values) reachable) (safe : valuesNoEval values) :
    globalsWithin (findLookups body) reachable ∧ hasEval body = false ∧
      globalsWithin (findEnvGlobals env) reachable ∧ bindingsNoEval env.v := by
  cases values with
  | nil => simp [FlatSem.doOpApp] at selected
  | cons function rest =>
    cases rest with
    | nil => simp [FlatSem.doOpApp] at selected
    | cons value tail =>
      cases tail with
      | cons extra tail => simp [FlatSem.doOpApp] at selected
      | nil =>
        have functionClosed := (findValuesGlobals_within_iff _ _).mp closed function (by simp)
        have valueClosed := (findValuesGlobals_within_iff _ _).mp closed value (by simp)
        have functionSafe := safe function (by simp)
        have valueSafe := safe value (by simp)
        cases function <;> simp only [FlatSem.doOpApp] at selected
        all_goals try contradiction
        case closure captured name expression =>
          simp only [Option.some.injEq, Prod.mk.injEq] at selected
          rcases selected with ⟨rfl, rfl⟩
          exact closureApplication_invariants captured name expression value reachable functionClosed functionSafe valueClosed valueSafe
        case recclosure captured funs name =>
          by_cases distinct : (funs.map Prod.fst).Nodup
          · simp only [distinct, ↓reduceIte] at selected
            cases found : findRecFun name funs with
            | none => simp [found] at selected
            | some entry =>
              obtain ⟨arg, expression⟩ := entry
              simp [found] at selected
              rcases selected with ⟨rfl, rfl⟩
              exact recclosureApplication_invariants captured funs name arg expression value reachable found functionClosed functionSafe valueClosed valueSafe
          · simp [distinct] at selected

/-- Dynamic evaluation is excluded by the simulation's Eval-free premise. This is a Flapjack proof helper with no separate HOL theorem. -/
theorem evaluate_keep_flatStateRel_appEval {C F : Type} (tra : BackendCommon.Tra)
    (args : List FlatLang.Exp) : evaluationSimulation (C := C) (F := F) [.app tra (.src .eval) args] := by
  intro env source next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have impossible := expressionsSafe (.app tra (.src .eval) args) (by simp)
  simp [hasEval] at impossible

end Flapjack.Compiler.Backend.FlatElim
