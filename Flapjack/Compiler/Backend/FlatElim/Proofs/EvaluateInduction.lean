import Flapjack.Compiler.Backend.FlatElim.Proofs.EvaluateThunk

/-! Bounded-state induction steps for the flat evaluation simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- Constructor simulation at a fixed source state. This is a Flapjack
induction helper for assembling the full evaluation theorem. -/
theorem evaluate_con_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra)
    (constructor : Option (FlatLang.CtorId × FlatLang.TypeId)) (args : List FlatLang.Exp)
    (ih : evaluationSimulationAt env source args.reverse) :
    evaluationSimulationAt env source [.con tra constructor args] := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have argsClosed : globalsWithin (findGlobalsList destGlobalVarLookup args.reverse) reachable := by
    apply findLookupsList_reverse_within args reachable
    simp only [findGlobalsList, findGlobals, globalsWithin_union] at lookupsClosed
    exact lookupsClosed.1
  have argsSafe : expressionsNoEval args.reverse := by
    apply expressionsNoEval_reverse args
    apply (hasEvalList_eq_false_iff args).mp
    have safe := expressionsSafe (.con tra constructor args) (by simp)
    simpa [hasEval] using safe
  cases argEval : FlatSem.evaluate env source args.reverse with
  | mk argState argResult =>
    simp only [FlatSem.evaluate, argEval] at run
    have argNotTypeError : argResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetArgState, targetArgEval, argRelated, argClosed, argSafe⟩ :=
      ih argState argResult reachable target argEval argsClosed related envClosed envSafe argsSafe argNotTypeError
    cases argResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨targetArgState, by simp [FlatSem.evaluate, targetArgEval], argRelated, argClosed, argSafe⟩
    | val values =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      have valuesClosed : globalsWithin (findValuesGlobals values.reverse) reachable := by
        apply findValuesGlobals_reverse_within
        simpa [findPrimitiveResultGlobals] using argClosed
      have valuesSafe : valuesNoEval values.reverse := by
        apply valuesNoEval_reverse
        simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using argSafe
      have valueClosed : globalsWithin (findValueGlobals (.conv constructor values.reverse)) reachable := by
        simpa [findValueGlobals] using valuesClosed
      have valueSafe : valueHasEval (.conv constructor values.reverse) = false := by
        simpa [valueHasEval] using (valuesHaveEval_eq_false_iff _).mpr valuesSafe
      have resultSafe := primitiveResult_value_invariants reachable (.conv constructor values.reverse) valueClosed valueSafe
      exact ⟨targetArgState, by simp [FlatSem.evaluate, targetArgEval], argRelated, resultSafe.1, resultSafe.2⟩

/-- Raise simulation at a fixed source state. This is a Flapjack
induction helper for assembling the full evaluation theorem. -/
theorem evaluate_raise_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (body : FlatLang.Exp)
    (ih : evaluationSimulationAt env source [body]) :
    evaluationSimulationAt env source [.raise tra body] := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have bodyClosed : globalsWithin (findGlobalsList destGlobalVarLookup [body]) reachable := by
    simp only [findGlobalsList, findGlobals, globalsWithin_union] at lookupsClosed ⊢
    exact lookupsClosed
  have bodySafe : expressionsNoEval [body] := by
    intro expression member
    simp only [List.mem_singleton] at member
    subst expression
    have safe := expressionsSafe (.raise tra body) (by simp)
    simpa [hasEval] using safe
  cases bodyEval : FlatSem.evaluate env source [body] with
  | mk bodyState bodyResult =>
    simp only [FlatSem.evaluate, bodyEval] at run
    have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetBodyState, targetBodyEval, bodyRelated, bodyResultClosed, bodyResultSafe⟩ :=
      ih bodyState bodyResult reachable target bodyEval bodyClosed related envClosed envSafe bodySafe bodyNotTypeError
    cases bodyResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨targetBodyState, by simp [FlatSem.evaluate, targetBodyEval], bodyRelated, bodyResultClosed, bodyResultSafe⟩
    | val values =>
      obtain ⟨value, rfl⟩ := Flapjack.Compiler.Backend.FlatProps.evaluate_sing env source bodyState body values bodyEval
      simp at run
      rcases run with ⟨rfl, rfl⟩
      have valueClosed : globalsWithin (findValueGlobals value) reachable := by
        have allClosed : globalsWithin (findValuesGlobals [value]) reachable := by
          simpa [findPrimitiveResultGlobals] using bodyResultClosed
        exact (findValuesGlobals_within_iff _ _).mp allClosed value (by simp)
      have valueSafe : valueHasEval value = false := by
        have allSafe : valuesNoEval [value] := by
          simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using bodyResultSafe
        exact allSafe value (by simp)
      have raisedSafe := primitiveResult_raise_invariants reachable value valueClosed valueSafe
      exact ⟨targetBodyState, by simp [FlatSem.evaluate, targetBodyEval], bodyRelated, raisedSafe.1, raisedSafe.2⟩

/-- Expression-list simulation at a fixed source state, with the tail
hypothesis available at clocks bounded by that state. This is a Flapjack
induction helper for assembling the full evaluation theorem. -/
theorem evaluate_list_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (headIH : evaluationSimulationAt env source [first])
    (tailIH : ∀ state : FlatSem.State C F, state.clock ≤ source.clock → evaluationSimulationAt env state (second :: rest)) :
    evaluationSimulationAt env source (first :: second :: rest) := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have headClosed : globalsWithin (findGlobalsList destGlobalVarLookup [first]) reachable := by
    apply (findLookupsList_within_iff _ _).mpr
    intro expression member
    simp only [List.mem_singleton] at member
    subst expression
    exact (findLookupsList_within_iff _ _).mp lookupsClosed first (by simp)
  have tailClosed : globalsWithin (findGlobalsList destGlobalVarLookup (second :: rest)) reachable := by
    apply (findLookupsList_within_iff _ _).mpr
    intro expression member
    exact (findLookupsList_within_iff _ _).mp lookupsClosed expression (by simp [member])
  have headSafe : expressionsNoEval [first] := by
    intro expression member
    simp only [List.mem_singleton] at member
    subst expression
    exact expressionsSafe first (by simp)
  have tailSafe : expressionsNoEval (second :: rest) := by
    intro expression member
    exact expressionsSafe expression (by simp [member])
  cases headEval : FlatSem.evaluate env source [first] with
  | mk headState headResult =>
    simp only [FlatSem.evaluate, headEval, FlatSem.fixClock] at run
    have headNotTypeError : headResult ≠ .err (.abort .typeError) := by
      intro bad
      subst headResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetHeadState, targetHeadEval, headRelated, headResultClosed, headResultSafe⟩ :=
      headIH headState headResult reachable target headEval headClosed related envClosed envSafe headSafe headNotTypeError
    have clampedRelated := flatStateRel_fixClock reachable source target headState targetHeadState headResult related headRelated
    simp only [FlatSem.fixClock] at clampedRelated
    cases headResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ targetHeadState with clock := min target.clock targetHeadState.clock }, ?_,
        clampedRelated, headResultClosed, headResultSafe⟩
      simp [FlatSem.evaluate, targetHeadEval, FlatSem.fixClock]
    | val heads =>
      obtain ⟨head, rfl⟩ := Flapjack.Compiler.Backend.FlatProps.evaluate_sing env source headState first heads headEval
      simp only at run
      cases tailEval : FlatSem.evaluate env { headState with clock := min source.clock headState.clock } (second :: rest) with
      | mk tailState tailResult =>
        simp only [tailEval] at run
        have tailNotTypeError : tailResult ≠ .err (.abort .typeError) := by
          intro bad
          subst tailResult
          simp at run
          rcases run with ⟨_, rfl⟩
          exact notTypeError rfl
        obtain ⟨targetTailState, targetTailEval, tailRelated, tailResultClosed, tailResultSafe⟩ :=
          tailIH _ (Nat.min_le_left _ _) tailState tailResult reachable _ tailEval tailClosed clampedRelated envClosed envSafe tailSafe tailNotTypeError
        cases tailResult with
        | err error =>
          simp only at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨targetTailState, ?_, tailRelated, tailResultClosed, tailResultSafe⟩
          simp [FlatSem.evaluate, targetHeadEval, FlatSem.fixClock, targetTailEval]
        | val tailValues =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          have headValueClosed : globalsWithin (findValueGlobals head) reachable := by
            have h : globalsWithin (findValuesGlobals [head]) reachable := by
              simpa [findPrimitiveResultGlobals] using headResultClosed
            exact (findValuesGlobals_within_iff _ _).mp h head (by simp)
          have headValueSafe : valueHasEval head = false := by
            have h : valuesNoEval [head] := by
              simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using headResultSafe
            exact h head (by simp)
          have valuesClosed : globalsWithin (findValuesGlobals (head :: tailValues)) reachable := by
            have tailValuesClosed : globalsWithin (findValuesGlobals tailValues) reachable := by
              simpa [findPrimitiveResultGlobals] using tailResultClosed
            simpa [findValuesGlobals, globalsWithin_union] using And.intro headValueClosed tailValuesClosed
          have valuesSafe : valuesNoEval (head :: tailValues) := by
            have tailValuesSafe : valuesNoEval tailValues := by
              simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using tailResultSafe
            intro value member
            rcases List.mem_cons.mp member with rfl | member
            · exact headValueSafe
            · exact tailValuesSafe value member
          refine ⟨targetTailState, ?_, tailRelated, ?_, ?_⟩
          · simp [FlatSem.evaluate, targetHeadEval, FlatSem.fixClock, targetTailEval]
          · simpa [findPrimitiveResultGlobals] using valuesClosed
          · simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using valuesSafe

/-- Ordinary primitive application simulation at a fixed source state. This
is a Flapjack induction helper for assembling the full evaluation theorem. -/
theorem evaluate_ordinary_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (ordinary : ordinaryPrimitive op) (ih : evaluationSimulationAt env source args.reverse) :
    evaluationSimulationAt env source [.app tra op args] := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have argsClosed : globalsWithin (findGlobalsList destGlobalVarLookup args.reverse) reachable := by
    apply findLookupsList_reverse_within args reachable
    have appClosed := (findLookupsList_within_iff _ _).mp lookupsClosed (.app tra op args) (by simp)
    exact (findLookups_app_within tra op args reachable appClosed).1
  have argsSafe : expressionsNoEval args.reverse := by
    apply expressionsNoEval_reverse args
    apply (hasEvalList_eq_false_iff args).mp
    have safe := expressionsSafe (.app tra op args) (by simp)
    simp [hasEval] at safe
    exact safe.2
  cases argEval : FlatSem.evaluate env source args.reverse with
  | mk argState argResult =>
    rw [evaluate_app_ordinary env source tra op args ordinary] at run
    simp only [argEval, FlatSem.fixClock] at run
    have argNotTypeError : argResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetArgState, targetArgEval, argRelated, argClosed, argSafe⟩ :=
      ih argState argResult reachable target argEval argsClosed related envClosed envSafe argsSafe argNotTypeError
    have clampedRelated := flatStateRel_fixClock reachable source target argState targetArgState argResult related argRelated
    simp only [FlatSem.fixClock] at clampedRelated
    cases argResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ targetArgState with clock := min target.clock targetArgState.clock }, ?_, clampedRelated, argClosed, argSafe⟩
      rw [evaluate_app_ordinary env target tra op args ordinary]
      simp [targetArgEval, FlatSem.fixClock]
    | val values =>
      simp only at run
      have valuesClosed : globalsWithin (findValuesGlobals values.reverse) reachable := by
        apply findValuesGlobals_reverse_within
        simpa [findPrimitiveResultGlobals] using argClosed
      have valuesSafe : valuesNoEval values.reverse := by
        apply valuesNoEval_reverse
        simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using argSafe
      have opClosed : globalsWithin (findLookups (.app tra op [])) reachable := by
        have appClosed := (findLookupsList_within_iff _ _).mp lookupsClosed (.app tra op args) (by simp)
        exact (findLookups_app_within tra op args reachable appClosed).2
      obtain ⟨targetNext, applied, nextRelated, closed, safe⟩ :=
        applyResult_flatStateRel reachable
          { argState with clock := min source.clock argState.clock }
          { targetArgState with clock := min target.clock targetArgState.clock }
          next op values.reverse result tra clampedRelated ordinary.1
          valuesClosed opClosed valuesSafe run notTypeError
      refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
      rw [evaluate_app_ordinary env target tra op args ordinary]
      simpa [targetArgEval, FlatSem.fixClock] using applied

/-- Recursive-binding simulation at a fixed source state. This is a
Flapjack induction helper for assembling the full evaluation theorem. -/
theorem evaluate_letrec_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (name : Flapjack.AstHOL.VarN)
    (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) (body : FlatLang.Exp)
    (bodyIH : ∀ newEnv, evaluationSimulationAt newEnv source [body]) :
    evaluationSimulationAt env source [.letrec name funs body] := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
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
      bodyIH { env with v := FlatSem.buildRecEnv funs env env.v } next result reachable target
        run bodyClosed related extended.1 extended.2 bodySafe notTypeError
    exact ⟨targetNext, by simpa [FlatSem.evaluate, distinct] using evaluated, nextRelated, closed, safe⟩
  · simp [FlatSem.evaluate, distinct] at run
    rcases run with ⟨_, rfl⟩
    exact (notTypeError rfl).elim

/-- Local-binding simulation at a fixed source state with the body
hypothesis available at bounded clocks. This is a Flapjack induction helper. -/
theorem evaluate_let_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra)
    (name : Option Flapjack.AstHOL.VarN) (first body : FlatLang.Exp)
    (firstIH : evaluationSimulationAt env source [first])
    (bodyIH : ∀ newEnv (newState : FlatSem.State C F), newState.clock ≤ source.clock →
      evaluationSimulationAt newEnv newState [body]) :
    evaluationSimulationAt env source [.let_ tra name first body] := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
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
      firstIH firstState firstResult reachable target firstEval firstClosed related envClosed envSafe firstSafe firstNotTypeError
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
          bodyIH env _ (Nat.min_le_left _ _) next result reachable _ run bodyClosed clampedRelated envClosed envSafe bodySafe notTypeError
        refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
        simpa [FlatSem.evaluate, targetFirstEval, FlatSem.fixClock] using evaluated
      | some name =>
        simp only at run
        have extendedClosed : globalsWithin (findEnvGlobals { env with v := (name, value) :: env.v }) reachable := by
          exact (bindingsWithin_cons name value env.v reachable).mpr ⟨valueClosed, envClosed⟩
        have extendedSafe : bindingsNoEval ((name, value) :: env.v) := by
          simpa [bindingsNoEval] using And.intro valueSafe envSafe
        obtain ⟨targetNext, evaluated, nextRelated, closed, safe⟩ :=
          bodyIH { env with v := (name, value) :: env.v } _ (Nat.min_le_left _ _) next result reachable _ run bodyClosed clampedRelated
            extendedClosed extendedSafe bodySafe notTypeError
        refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
        simpa [FlatSem.evaluate, targetFirstEval, FlatSem.fixClock] using evaluated

/-- Conditional simulation at a fixed source state with branch hypotheses
available at bounded clocks. This is a Flapjack induction helper. -/
theorem evaluate_if_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (cond yes no : FlatLang.Exp)
    (condIH : evaluationSimulationAt env source [cond])
    (yesIH : ∀ newState : FlatSem.State C F, newState.clock ≤ source.clock → evaluationSimulationAt env newState [yes])
    (noIH : ∀ newState : FlatSem.State C F, newState.clock ≤ source.clock → evaluationSimulationAt env newState [no]) :
    evaluationSimulationAt env source [.if_ tra cond yes no] := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
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
      condIH condState condResult reachable target condEval condClosed related envClosed envSafe condSafe condNotTypeError
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
            yesIH _ (Nat.min_le_left _ _) next result reachable _ run yesClosed clampedRelated envClosed envSafe yesSafe notTypeError
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
            noIH _ (Nat.min_le_left _ _) next result reachable _ run noClosed clampedRelated envClosed envSafe noSafe notTypeError
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

/-- Apply the selected-row induction hypothesis at a bounded source clock.
This is a Flapjack induction helper. -/
theorem evaluate_selectedRow_bounded {C F : Type} (rows : List (FlatLang.Pat × FlatLang.Exp)) (clock : Nat)
    (rowIH : ∀ pattern body, (pattern, body) ∈ rows → ∀ newEnv (newState : FlatSem.State C F),
      newState.clock ≤ clock → evaluationSimulationAt newEnv newState [body])
    (env : FlatSem.Environment FlatSem.Value) (source target next : FlatSem.State C F)
    (stateBound : source.clock ≤ clock) (reachable : NumSet) (value noMatch : FlatSem.Value)
    (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value)) (body : FlatLang.Exp)
    (result : Result (List FlatSem.Value) FlatSem.Value)
    (selected : FlatSem.selectRow source rows value noMatch = .ok (bindings, body))
    (run : FlatSem.evaluate { env with v := bindings ++ env.v } source [body] = (next, result))
    (related : flatStateRel reachable source target)
    (rowsClosed : globalsWithin (findGlobalsPats destGlobalVarLookup rows) reachable) (rowsSafe : hasEvalPats rows = false)
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
  exact rowIH pattern body member { env with v := bindings ++ env.v } source stateBound next result reachable target run
    (singletonLookups_within body reachable invariants.1) related
    (bindingsWithin_append bindings env.v reachable invariants.2.2.1 envClosed)
    (bindingsNoEval_append bindings env.v invariants.2.2.2 envSafe)
    (singletonExpression_noEval body invariants.2.1) notTypeError

/-- Mat simulation at a fixed source state with row hypotheses
available at bounded clocks. This is a Flapjack induction helper. -/
theorem evaluate_mat_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (body : FlatLang.Exp)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (bodyIH : evaluationSimulationAt env source [body])
    (rowIH : ∀ pattern branch, (pattern, branch) ∈ rows → ∀ newEnv (newState : FlatSem.State C F),
      newState.clock ≤ source.clock → evaluationSimulationAt newEnv newState [branch]) :
    evaluationSimulationAt env source [.mat tra body rows] := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
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
      bodyIH bodyState bodyResult reachable target bodyEval bodyClosed related envClosed envSafe bodySafe bodyNotTypeError
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
          evaluate_selectedRow_bounded rows source.clock rowIH env _ _ next (Nat.min_le_left _ _) reachable value FlatSem.bindExnV bindings branch result
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

/-- Handle simulation at a fixed source state with row hypotheses
available at bounded clocks. This is a Flapjack induction helper. -/
theorem evaluate_handle_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (body : FlatLang.Exp)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (bodyIH : evaluationSimulationAt env source [body])
    (rowIH : ∀ pattern branch, (pattern, branch) ∈ rows → ∀ newEnv (newState : FlatSem.State C F),
      newState.clock ≤ source.clock → evaluationSimulationAt newEnv newState [branch]) :
    evaluationSimulationAt env source [.handle tra body rows] := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have expressionClosed := (findLookupsList_within_iff _ _).mp lookupsClosed (.handle tra body rows) (by simp)
  simp only [findLookups, findGlobals, globalsWithin_union] at expressionClosed
  have bodyClosed := singletonLookups_within body reachable expressionClosed.1
  have expressionSafe := expressionsSafe (.handle tra body rows) (by simp)
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
      bodyIH bodyState bodyResult reachable target bodyEval bodyClosed related envClosed envSafe bodySafe bodyNotTypeError
    have clampedRelated := flatStateRel_fixClock reachable source target bodyState targetBodyState bodyResult related bodyRelated
    simp only [FlatSem.fixClock] at clampedRelated
    cases bodyResult with
    | val values =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ targetBodyState with clock := min target.clock targetBodyState.clock }, ?_,
        clampedRelated, bodyResultClosed, bodyResultSafe⟩
      simp [FlatSem.evaluate, targetBodyEval, FlatSem.fixClock]
    | err error =>
      cases error with
      | abort reason =>
        simp only at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨{ targetBodyState with clock := min target.clock targetBodyState.clock }, ?_,
          clampedRelated, bodyResultClosed, bodyResultSafe⟩
        simp [FlatSem.evaluate, targetBodyEval, FlatSem.fixClock]
      | raise value =>
        have valueClosed : globalsWithin (findValueGlobals value) reachable := by
          simpa [findPrimitiveResultGlobals, findResultGlobals] using bodyResultClosed
        have valueSafe : valueHasEval value = false := by
          simpa [Flapjack.Compiler.Backend.FlatProps.resultValues, valuesNoEval] using bodyResultSafe
        simp only at run
        split at run
        · rename_i error selected
          simp only [bodyEval] at selected
          change FlatSem.selectRow { bodyState with clock := min source.clock bodyState.clock } rows value value = .error error at selected
          have shape := selectRow_error _ rows value value error selected
          rcases shape with bad | raised
          · subst error
            simp at run
            rcases run with ⟨_, rfl⟩
            exact (notTypeError rfl).elim
          · subst error
            rcases run with ⟨rfl, rfl⟩
            refine ⟨{ targetBodyState with clock := min target.clock targetBodyState.clock }, ?_,
              clampedRelated, bodyResultClosed, bodyResultSafe⟩
            rw [FlatSem.evaluate]
            simp only [targetBodyEval, FlatSem.fixClock]
            split
            · rename_i targetError targetSelected
              simp only [targetBodyEval] at targetSelected
              change FlatSem.selectRow { targetBodyState with clock := min target.clock targetBodyState.clock } rows value value = .error targetError at targetSelected
              have sameSelection := selectRow_related reachable _ _ rows value value clampedRelated
              have same : targetError = .raise value := Except.error.inj (targetSelected.symm.trans (sameSelection.trans selected))
              subst targetError
              rfl
            · rename_i targetBindings targetBranch targetSelected
              simp only [targetBodyEval] at targetSelected
              change FlatSem.selectRow { targetBodyState with clock := min target.clock targetBodyState.clock } rows value value = .ok (targetBindings, targetBranch) at targetSelected
              have sameSelection := selectRow_related reachable _ _ rows value value clampedRelated
              have impossible := targetSelected.symm.trans (sameSelection.trans selected)
              cases impossible
        · rename_i bindings branch selected
          simp only [bodyEval] at selected
          change FlatSem.selectRow { bodyState with clock := min source.clock bodyState.clock } rows value value = .ok (bindings, branch) at selected
          obtain ⟨targetNext, evaluated, nextRelated, closed, safe⟩ :=
            evaluate_selectedRow_bounded rows source.clock rowIH env _ _ next (Nat.min_le_left _ _) reachable value value bindings branch result
              selected run clampedRelated expressionClosed.2 expressionSafe.2 valueClosed valueSafe envClosed envSafe notTypeError
          refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
          rw [FlatSem.evaluate]
          simp only [targetBodyEval, FlatSem.fixClock]
          split
          · rename_i targetError targetSelected
            simp only [targetBodyEval] at targetSelected
            change FlatSem.selectRow { targetBodyState with clock := min target.clock targetBodyState.clock } rows value value = .error targetError at targetSelected
            have sameSelection := selectRow_related reachable _ _ rows value value clampedRelated
            have impossible := targetSelected.symm.trans (sameSelection.trans selected)
            cases impossible
          · rename_i targetBindings targetBranch targetSelected
            simp only [targetBodyEval] at targetSelected
            change FlatSem.selectRow { targetBodyState with clock := min target.clock targetBodyState.clock } rows value value = .ok (targetBindings, targetBranch) at targetSelected
            have sameSelection := selectRow_related reachable _ _ rows value value clampedRelated
            have same : (targetBindings, targetBranch) = (bindings, branch) := Except.ok.inj (targetSelected.symm.trans (sameSelection.trans selected))
            cases same
            exact evaluated

end Flapjack.Compiler.Backend.FlatElim
