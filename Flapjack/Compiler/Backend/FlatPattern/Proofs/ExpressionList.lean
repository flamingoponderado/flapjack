import Flapjack.Compiler.Backend.FlatPattern.Proofs.ExpressionCases

/-! Ordered expression-list simulation for the flat pattern compiler. The
underlying evaluator and value/state relations remain pending HOL review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Compiling an expression list maps each expression in order. -/
theorem compileExps_rows (cfg : Config) (expressions : List FlatLang.Exp) :
    (compileExps cfg expressions).2.2 = expressions.map (fun expression => (compileExp cfg expression).2.2) := by
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
    cases first : compileExp cfg expression with
    | mk bound part =>
      cases part with
      | mk flag compiled =>
        cases tail : compileExps cfg rest with
        | mk tailBound part =>
          cases part with
          | mk tailFlag compiledTail => simpa [compileExps, first, tail] using ih

/-- List compilation bounds the head and tail compiler measures. -/
theorem compileExps_cons_bounds (cfg : Config) (first : FlatLang.Exp) (rest : List FlatLang.Exp) :
    (compileExp cfg first).1 ≤ (compileExps cfg (first :: rest)).1 ∧
      (compileExps cfg rest).1 ≤ (compileExps cfg (first :: rest)).1 := by
  cases head : compileExp cfg first with
  | mk bound part =>
    cases part with
    | mk flag compiled =>
      cases tail : compileExps cfg rest with
      | mk tailBound part =>
        cases part with
        | mk tailFlag compiledTail => simp [compileExps, head, tail]; omega

/-- An error in the first expression stops a nonempty expression list. -/
theorem evaluate_list_first_error {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (firstRun : FlatSem.evaluate env state [first] = (next, .err error)) :
    FlatSem.evaluate env state (first :: second :: rest) =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, firstRun, FlatSem.fixClock]

/-- A successful first expression followed by an error propagates the error. -/
theorem evaluate_list_tail_error {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next final : FlatSem.State C F) (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (value : FlatSem.Value) (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (firstRun : FlatSem.evaluate env state [first] = (next, .val [value]))
    (tailRun : FlatSem.evaluate env { next with clock := min state.clock next.clock } (second :: rest) = (final, .err error)) :
    FlatSem.evaluate env state (first :: second :: rest) = (final, .err error) := by
  simp [FlatSem.evaluate, firstRun, FlatSem.fixClock, tailRun]

/-- Successful nonempty expression lists preserve the first result and tail order. -/
theorem evaluate_list_values {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next final : FlatSem.State C F) (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (value : FlatSem.Value) (values : List FlatSem.Value)
    (firstRun : FlatSem.evaluate env state [first] = (next, .val [value]))
    (tailRun : FlatSem.evaluate env { next with clock := min state.clock next.clock } (second :: rest) = (final, .val values)) :
    FlatSem.evaluate env state (first :: second :: rest) = (final, .val (value :: values)) := by
  simp [FlatSem.evaluate, firstRun, FlatSem.fixClock, tailRun]

/-- Forward simulation for an expression list, parameterized by the expression
induction hypotheses for its members. -/
def ExpressionsSimulation {C F : Type} (cfg stateCfg : Config) (expressions : List FlatLang.Exp) : Prop :=
  ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
    (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
    FlatSem.evaluate sourceEnv source expressions = (sourceFinal, sourceResult) →
    EnvRel n sourceEnv targetEnv → StateRel stateCfg source target → (compileExps cfg expressions).1 < n →
    sourceResult ≠ .err (.abort .typeError) →
    ∃ targetFinal targetResult,
      FlatSem.evaluate targetEnv target (compileExps cfg expressions).2.2 = (targetFinal, targetResult) ∧
      StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult

/-- Compiling an expression list preserves evaluation when each member satisfies
the expression induction hypothesis. -/
theorem compileExps_simulation {C F : Type} (cfg stateCfg : Config) (expressions : List FlatLang.Exp)
    (membersIH : ∀ expression ∈ expressions, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression) :
    ExpressionsSimulation (C := C) (F := F) cfg stateCfg expressions := by
  induction expressions with
  | nil =>
    intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
    simp [FlatSem.evaluate] at sourceEval
    rcases sourceEval with ⟨rfl, rfl⟩
    exact ⟨target, .val [], by simp [compileExps, FlatSem.evaluate], states, .values .nil⟩
  | cons first rest ih =>
    have firstIH := membersIH first (by simp)
    have restIH : ∀ expression ∈ rest, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression := by
      intro expression member
      exact membersIH expression (List.mem_cons_of_mem _ member)
    cases rest with
    | nil =>
      intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
      have firstBound : (compileExp cfg first).1 < n := by
        have bounds := compileExps_cons_bounds cfg first []
        omega
      obtain ⟨targetFinal, targetResult, targetRun, finalRel, resultRel⟩ :=
        firstIH sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states firstBound safe
      exact ⟨targetFinal, targetResult, by simpa [compileExps_rows] using targetRun, finalRel, resultRel⟩
    | cons second rest =>
      have tailSim := ih restIH
      intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
      have bounds := compileExps_cons_bounds cfg first (second :: rest)
      have firstBound : (compileExp cfg first).1 < n := by omega
      have tailBound : (compileExps cfg (second :: rest)).1 < n := by omega
      cases firstRun : FlatSem.evaluate sourceEnv source [first] with
      | mk sourceNext firstResult =>
        have firstSafe : firstResult ≠ .err (.abort .typeError) := by
          intro bad
          subst firstResult
          have outer := evaluate_list_first_error sourceEnv source sourceNext first second rest (.abort .typeError) firstRun
          rw [sourceEval] at outer
          exact safe (congrArg Prod.snd outer)
        obtain ⟨targetNext, targetFirstResult, targetFirstRun, nextStates, firstRelated⟩ := firstIH
          sourceEnv targetEnv source target sourceNext firstResult n firstRun envs states firstBound firstSafe
        cases firstRelated with
        | error errorsRel =>
          rename_i leftError rightError
          have sourceOuter := evaluate_list_first_error sourceEnv source sourceNext first second rest leftError firstRun
          have targetOuter := evaluate_list_first_error targetEnv target targetNext (compileExp cfg first).2.2
            ((compileExp cfg second).2.2) (rest.map (fun expression => (compileExp cfg expression).2.2)) rightError targetFirstRun
          have equal := sourceEval.symm.trans sourceOuter
          cases equal
          exact ⟨_, _, by simpa [compileExps_rows] using targetOuter,
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
            cases tailRun : FlatSem.evaluate sourceEnv sourceFixed (second :: rest) with
            | mk sourceLast tailResult =>
              have tailSafe : tailResult ≠ .err (.abort .typeError) := by
                intro bad
                subst tailResult
                have outer := evaluate_list_tail_error sourceEnv source sourceNext sourceLast first second rest value
                  (.abort .typeError) firstRun tailRun
                rw [sourceEval] at outer
                exact safe (congrArg Prod.snd outer)
              obtain ⟨targetLast, targetTailResult, targetTailRun, finalRel, tailRelated⟩ := tailSim
                sourceEnv targetEnv sourceFixed targetFixed sourceLast tailResult n tailRun envs fixedStates tailBound tailSafe
              cases tailRelated with
              | error errorsRel =>
                rename_i leftError rightError
                have sourceOuter := evaluate_list_tail_error sourceEnv source sourceNext sourceLast first second rest value
                  leftError firstRun tailRun
                have targetOuter := evaluate_list_tail_error targetEnv target targetNext targetLast (compileExp cfg first).2.2
                  ((compileExp cfg second).2.2) (rest.map (fun expression => (compileExp cfg expression).2.2)) value'
                  rightError targetFirstRun (by simpa [compileExps_rows] using targetTailRun)
                have equal := sourceEval.symm.trans sourceOuter
                cases equal
                exact ⟨targetLast, _, by simpa [compileExps_rows] using targetOuter, finalRel, .error errorsRel⟩
              | values tailValuesRel =>
                rename_i sourceTailValues targetTailValues
                have sourceOuter := evaluate_list_values sourceEnv source sourceNext sourceLast first second rest value
                  sourceTailValues firstRun tailRun
                have targetOuter := evaluate_list_values targetEnv target targetNext targetLast (compileExp cfg first).2.2
                  ((compileExp cfg second).2.2) (rest.map (fun expression => (compileExp cfg expression).2.2)) value'
                  targetTailValues targetFirstRun (by simpa [compileExps_rows] using targetTailRun)
                have equal := sourceEval.symm.trans sourceOuter
                cases equal
                exact ⟨targetLast, _, by simpa [compileExps_rows] using targetOuter, finalRel,
                  .values (.cons valueRel tailValuesRel)⟩

/-- The compilation bound for a list is below a positive limit exactly when
all its members have bounds below that limit. -/
theorem compileExps_bound_iff (cfg : Config) (expressions : List FlatLang.Exp) (n : Nat) (positive : 0 < n) :
    (compileExps cfg expressions).1 < n ↔ ∀ expression ∈ expressions, (compileExp cfg expression).1 < n := by
  induction expressions with
  | nil => simp [compileExps, positive]
  | cons first rest ih =>
    cases head : compileExp cfg first with
    | mk headBound part =>
      cases part with
      | mk headFlag headBody =>
        cases tail : compileExps cfg rest with
        | mk tailBound part =>
          cases part with
          | mk tailFlag tailBody =>
            simp only [compileExps, head, tail, List.mem_cons, forall_eq_or_imp] at ih ⊢
            constructor
            · intro bound
              exact ⟨by omega, ih.mp (by omega)⟩
            · intro ⟨firstBound, restBound⟩
              have tailBoundLt := ih.mpr restBound
              omega

/-- Reversing an expression list does not change whether its compilation bound
is below a positive limit. -/
theorem compileExps_reverse_bound (cfg : Config) (expressions : List FlatLang.Exp) (n : Nat)
    (bound : (compileExps cfg expressions).1 < n) : (compileExps cfg expressions.reverse).1 < n := by
  have positive : 0 < n := by omega
  apply (compileExps_bound_iff cfg expressions.reverse n positive).2
  intro expression member
  exact (compileExps_bound_iff cfg expressions n positive).1 bound expression (by simpa using member)

/-- Constructor evaluation wraps a successful argument list in one value. -/
theorem evaluate_con_values {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra)
    (tag : Option (FlatLang.CtorId × FlatLang.TypeId)) (args : List FlatLang.Exp) (values : List FlatSem.Value)
    (run : FlatSem.evaluate env state args.reverse = (next, .val values)) :
    FlatSem.evaluate env state [.con trace tag args] = (next, .val [.conv tag values.reverse]) := by
  simp [FlatSem.evaluate, run]

/-- Constructor evaluation propagates argument errors unchanged. -/
theorem evaluate_con_error {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra)
    (tag : Option (FlatLang.CtorId × FlatLang.TypeId)) (args : List FlatLang.Exp)
    (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state args.reverse = (next, .err error)) :
    FlatSem.evaluate env state [.con trace tag args] = (next, .err error) := by
  simp [FlatSem.evaluate, run]

/-- Reversing related value lists preserves their pointwise relation. -/
theorem valueRel_reverse {left right : List FlatSem.Value} (related : List.Forall₂ ValueRel left right) :
    List.Forall₂ ValueRel left.reverse right.reverse := by
  have appendRel : ∀ {a b c d : List FlatSem.Value}, List.Forall₂ ValueRel a b →
      List.Forall₂ ValueRel c d → List.Forall₂ ValueRel (a ++ c) (b ++ d) := by
    intro a b c d first second
    induction first with
    | nil => exact second
    | cons head tail ih => exact .cons head ih
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
    simp only [List.reverse_cons]
    exact appendRel ih (.cons head .nil)

/-- Constructor expressions preserve the forward simulation when their
argument expressions satisfy the induction hypotheses. -/
theorem compile_con_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (tag : Option (FlatLang.CtorId × FlatLang.TypeId)) (args : List FlatLang.Exp)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.con trace tag args) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
  cases compiled : compileExps cfg args with
  | mk argsBound result =>
    cases result with
    | mk flag compiledArgs =>
      have argsBoundLt : (compileExps cfg args).1 < n := by simpa [compileExp, compiled] using bound
      have reversedBound := compileExps_reverse_bound cfg args n argsBoundLt
      have reversedIH : ∀ expression ∈ args.reverse, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression := by
        intro expression member
        exact argumentsIH expression (by simpa using member)
      have listSim := compileExps_simulation cfg stateCfg args.reverse reversedIH
      cases argsRun : FlatSem.evaluate sourceEnv source args.reverse with
      | mk sourceNext argsResult =>
        have argsSafe : argsResult ≠ .err (.abort .typeError) := by
          intro bad
          subst argsResult
          have outer := evaluate_con_error sourceEnv source sourceNext trace tag args (.abort .typeError) argsRun
          rw [sourceEval] at outer
          exact safe (congrArg Prod.snd outer)
        obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := listSim
          sourceEnv targetEnv source target sourceNext argsResult n argsRun envs states reversedBound argsSafe
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

end Flapjack.Compiler.Backend.FlatPattern
