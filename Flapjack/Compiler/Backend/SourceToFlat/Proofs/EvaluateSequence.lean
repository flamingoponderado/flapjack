import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateEmptyDeclarations
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EnvironmentDomain
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDletrec
import Flapjack.EvaluateHOL.ClockFull

/-! Sequential declaration composition for the source-to-flat simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Declaration simulation restricted to a source clock bound. -/
def FactoredDecBoundedIH {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (decs : List Dec) : Prop :=
  ∀ (genv : GlobalEnv) (env nextEnv : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (source sourceLast : State F) (flat : FlatSem.State C F) (start finish next : NextIndices)
    (other : Set (Nat × IndexKind)) (n n' : Nat) (gen nextGen : EnvironmentGenerationStore)
    (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value),
    source.clock ≤ limit → EvaluateHOL.evaluateDecs source sourceEnv decs = (sourceLast, result) →
    factoredInvariant interp transform gen genv (start, finish, other) source flat →
    compileDecs trace n start env gen decs = (n', next, nextEnv, nextGen, flatDecs) →
    GlobalEnvInv genv env (fun _ => False) sourceEnv →
    result ≠ .err (.abort .typeError) → envGenRel gen source.evalState →
    envGenFutureRel interp nextGen source.evalState → idxPrev next finish →
    FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen nextEnv flatDecs result

/-- Declaration induction at a strictly smaller clock. This is the form
needed for dynamic evaluation; unlike an unbounded hypothesis it can be
supplied by well-founded induction on the evaluator clock. -/
def FactoredDecClockIH {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat) : Prop :=
  ∀ (decs : List Dec) (genv : GlobalEnv) (env nextEnv : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (source sourceLast : State F) (flat : FlatSem.State C F) (start finish next : NextIndices)
    (other : Set (Nat × IndexKind)) (n n' : Nat) (gen nextGen : EnvironmentGenerationStore)
    (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value),
    source.clock < limit → EvaluateHOL.evaluateDecs source sourceEnv decs = (sourceLast, result) →
    factoredInvariant interp transform gen genv (start, finish, other) source flat →
    compileDecs trace n start env gen decs = (n', next, nextEnv, nextGen, flatDecs) →
    GlobalEnvInv genv env (fun _ => False) sourceEnv →
    result ≠ .err (.abort .typeError) → envGenRel gen source.evalState →
    envGenFutureRel interp nextGen source.evalState → idxPrev next finish →
    FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen nextEnv flatDecs result

/-- Bounded declaration simulations below a limit supply the declaration
hypothesis used by a smaller-clock dynamic evaluation. -/
theorem factoredDecClockIH_of_smaller {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (smaller : ∀ n, n < limit → ∀ decs, FactoredDecBoundedIH (F := F) interp transform n decs) :
    FactoredDecClockIH (F := F) interp transform limit := by
  intro decs genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result below
  exact smaller source.clock below decs genv env nextEnv sourceEnv trace source sourceLast flat
    start finish next other n n' gen nextGen flatDecs result (Nat.le_refl _)

/-- Empty declaration lists satisfy the factored induction hypothesis. -/
theorem factoredDecBoundedIH_empty {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat) :
    FactoredDecBoundedIH (F := F) interp transform limit [] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result _ sourceRun invariant compiled envInv notTypeError generation future bounded
  exact evaluateDecs_empty_case interp transform genv env nextEnv sourceEnv trace source sourceLast flat
    start finish next other n n' gen nextGen flatDecs result sourceRun invariant compiled envInv notTypeError
    generation future bounded

/-- Type-abbreviation declarations satisfy the factored induction hypothesis. -/
theorem factoredDecBoundedIH_dtabbrev {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (location : Flapjack.Misc.Location.Locs) (typeVars : List TvarN) (name : TypeN) (typ : AstT) :
    FactoredDecBoundedIH (F := F) interp transform limit [.dtabbrev location typeVars name typ] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result _ sourceRun invariant compiled envInv notTypeError generation future bounded
  exact evaluateDtabbrev_case interp transform genv env nextEnv sourceEnv trace source sourceLast flat
    start finish next other n n' gen nextGen location typeVars name typ flatDecs result sourceRun invariant compiled
    envInv notTypeError generation future bounded

/-- Recursive declarations satisfy the factored induction hypothesis. -/
theorem factoredDecBoundedIH_dletrec {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (location : Flapjack.Misc.Location.Locs) (funs : List (VarN × VarN × AstHOL.Exp)) :
    FactoredDecBoundedIH (F := F) interp transform limit [.dletrec location funs] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result _ sourceRun invariant compiled envInv notTypeError generation future bounded
  exact evaluateDletrec_case_factored interp transform genv env nextEnv sourceEnv trace funs source sourceLast flat
    start finish next other n n' gen nextGen location flatDecs result sourceRun invariant compiled envInv
    notTypeError generation future bounded

/-- Environment declarations satisfy the factored induction hypothesis,
including the oracle and generation updates. -/
theorem factoredDecBoundedIH_denv {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat) (name : VarN) :
    FactoredDecBoundedIH (F := F) interp transform limit [.denv name] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result _ sourceRun invariant compiled envInv notTypeError generation future bounded
  have futureCompiled : envGenFutureRel interp (compileDecs trace n start env gen [.denv name]).2.2.2.1
      source.evalState := by simpa [compiled] using future
  have boundedCompiled : idxPrev (compileDecs trace n start env gen [.denv name]).2.1 finish := by
    simpa [compiled] using bounded
  obtain ⟨value, after, stateEq, resultEq, flatRun, finalInvariant, growth, _, states, finalGeneration,
    forward, finalEnv, domain⟩ :=
    evaluateDenv_factored_result interp transform genv source sourceLast flat sourceEnv result trace n start
      finish other env gen name sourceRun invariant generation notTypeError envInv futureCompiled boundedCompiled
  subst sourceLast
  subst result
  simp only [compiled] at flatRun finalInvariant finalGeneration finalEnv domain
  refine ⟨_, _, none, flatRun, states, ?_, ?_, ?_⟩
  · intro _
    exact ⟨finalInvariant, forward, growth⟩
  · intro resultEnv same
    cases same
    exact ⟨rfl, domain, finalGeneration, finalEnv⟩
  · intro error impossible
    cases impossible

/-- The source-safety condition for a value declaration excludes a type
error from its initializer. -/
theorem dlet_expression_safe {F : Type} (source : State F) (env : SemEnv Value)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (safe : ∀ last, EvaluateHOL.evaluateDecs source env [.dlet location pattern expr] ≠
      (last, .err (.abort .typeError))) :
    ∀ last, EvaluateHOL.evaluate source env [expr] ≠ (last, .err (.abort .typeError)) := by
  obtain ⟨distinct, wellformed⟩ := dlet_conditions_of_safe source env location pattern expr safe
  intro last bad
  apply safe last
  simp [EvaluateHOL.evaluateDecs, distinct, wellformed, bad]

/-- Compose a successful first declaration with a tail induction hypothesis.
The tail hypothesis has the same invariant, environment, generation and
future premises as the declaration compiler theorem; it does not assume a
target execution or any postconditions. The factored relations still need
HOL correspondence review. -/
theorem factoredDecCase_append_success {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (baseMap firstMap tailMap : Environment)
    (baseEnv firstEnv : SemEnv Value) (source middle last : State F) (flat : FlatSem.State C F)
    (finish firstNext lastNext : NextIndices) (other : Set (Nat × IndexKind))
    (firstGen lastGen : EnvironmentGenerationStore) (firstCode tailCode : List FlatLang.Exp)
    (tailResult : Result (SemEnv Value) Value)
    (baseInv : GlobalEnvInv genv baseMap (fun _ => False) baseEnv)
    (future : envGenFutureRel interp lastGen source.evalState)
    (firstCase : FactoredDecCase interp transform genv source middle flat finish firstNext other firstGen
      firstMap firstCode (.val firstEnv))
    (tailIH : ∀ midGenv midFlat,
      factoredInvariant interp transform firstGen midGenv (firstNext, finish, other) middle midFlat →
      GlobalEnvInv midGenv (extendEnv firstMap baseMap) (fun _ => False) (extendDecEnv firstEnv baseEnv) →
      envGenRel firstGen middle.evalState → envGenFutureRel interp lastGen middle.evalState →
      FactoredDecCase interp transform midGenv middle last midFlat finish lastNext other lastGen tailMap
        tailCode tailResult) :
    FactoredDecCase interp transform genv source last flat finish lastNext other lastGen
      (extendEnv tailMap firstMap) (firstCode ++ tailCode) (combineDecResult firstEnv tailResult) := by
  obtain ⟨midFlat, midGenv, firstError, firstRun, _, firstPost, firstSuccess, _⟩ := firstCase
  obtain ⟨firstInvariant, firstForward, firstGrowth⟩ := firstPost trivial
  obtain ⟨firstNone, firstDomain, firstGeneration, firstEnvInv⟩ := firstSuccess firstEnv rfl
  subst firstError
  have baseMid := globalEnvInv_growth genv midGenv firstGrowth baseMap (fun _ => False) baseEnv baseInv
  have combinedInv := globalEnvInv_append_factored midGenv firstMap baseMap firstEnv baseEnv
    ⟨firstDomain, firstEnvInv, baseMid⟩
  have futureMid := envGenFutureRel_forward interp lastGen source.evalState middle.evalState ⟨future, firstForward⟩
  obtain ⟨lastFlat, lastGenv, tailError, tailRun, lastStates, tailPost, tailSuccess, tailErrors⟩ :=
    tailIH midGenv midFlat firstInvariant combinedInv firstGeneration futureMid
  have flatRun : FlatSem.evaluateDecs flat (firstCode ++ tailCode) = (lastFlat, tailError) := by
    rw [FlatSem.evaluateDecs_append, firstRun]
    exact tailRun
  refine ⟨lastFlat, lastGenv, tailError, flatRun, lastStates, ?_⟩
  cases tailResult with
  | val tailEnv =>
    obtain ⟨finalInvariant, tailForward, tailGrowth⟩ := tailPost trivial
    obtain ⟨noError, tailDomain, tailGeneration, tailEnvInv⟩ := tailSuccess tailEnv rfl
    have firstFinal := globalEnvInv_growth midGenv lastGenv tailGrowth firstMap (fun _ => False) firstEnv firstEnvInv
    refine ⟨?_, ?_, ?_⟩
    · intro _
      exact ⟨finalInvariant, oracForwardRel_trans interp _ _ _ ⟨firstForward, tailForward⟩,
        firstGrowth.trans tailGrowth⟩
    · intro resultEnv same
      simp only [combineDecResult, Result.val.injEq] at same
      subst resultEnv
      exact ⟨noError, envDomainEq_append tailMap firstMap tailEnv firstEnv ⟨tailDomain, firstDomain⟩,
        tailGeneration, globalEnvInv_append_factored lastGenv tailMap firstMap tailEnv firstEnv
          ⟨tailDomain, tailEnvInv, firstFinal⟩⟩
    · intro error impossible
      cases impossible
  | err error =>
    obtain ⟨flatErr, isError, related⟩ := tailErrors error rfl
    refine ⟨?_, ?_, ?_⟩
    · intro notAbort
      cases error with
      | abort kind => exact False.elim notAbort
      | raise value =>
        obtain ⟨finalInvariant, tailForward, tailGrowth⟩ := tailPost trivial
        exact ⟨finalInvariant, oracForwardRel_trans interp _ _ _ ⟨firstForward, tailForward⟩,
          firstGrowth.trans tailGrowth⟩
    · intro resultEnv impossible
      cases impossible
    · intro error' same
      simp only [combineDecResult, Result.err.injEq] at same
      subst error'
      exact ⟨flatErr, isError, related⟩

/-- A first-declaration error stops the flat sequence. For a raised error,
the reserved range and generation are advanced to the complete compiler
output using the compiler's index and generation-validity facts. -/
theorem factoredDecCase_append_error {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (firstMap tailMap : Environment) (source last : State F)
    (flat : FlatSem.State C F) (finish firstNext lastNext : NextIndices) (other : Set (Nat × IndexKind))
    (firstGen lastGen : EnvironmentGenerationStore) (firstCode tailCode : List FlatLang.Exp)
    (error : ErrorResult Value)
    (firstCase : FactoredDecCase interp transform genv source last flat finish firstNext other firstGen
      firstMap firstCode (.err error))
    (previous : idxPrev firstNext lastNext) (bounded : idxPrev lastNext finish)
    (lastGenValid : envGenInv lastGen) :
    FactoredDecCase interp transform genv source last flat finish lastNext other lastGen
      (extendEnv tailMap firstMap) (firstCode ++ tailCode) (.err error) := by
  obtain ⟨finalFlat, finalGenv, flatError, firstRun, states, post, _, errors⟩ := firstCase
  obtain ⟨flatErr, isError, related⟩ := errors error rfl
  subst flatError
  have flatRun : FlatSem.evaluateDecs flat (firstCode ++ tailCode) = (finalFlat, some flatErr) := by
    rw [FlatSem.evaluateDecs_append, firstRun]
  refine ⟨finalFlat, finalGenv, some flatErr, flatRun, states, ?_, ?_, ?_⟩
  · intro notAbort
    cases error with
    | abort kind => exact False.elim notAbort
    | raise value =>
      obtain ⟨invariant, forward, growth⟩ := post trivial
      exact ⟨invariantIdxRangeShrinkGen interp transform firstGen lastGen finalGenv
        firstNext lastNext finish other last finalFlat
        ⟨invariant, previous, bounded, fun _ => lastGenValid⟩, forward, growth⟩
  · intro resultEnv impossible
    cases impossible
  · intro error' same
    cases same
    exact ⟨flatErr, rfl, related⟩

/-- Clock-bounded declaration simulations compose in source order. -/
theorem factoredDecBoundedIH_cons {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (first second : Dec) (rest : List Dec)
    (firstIH : FactoredDecBoundedIH (F := F) interp transform limit [first])
    (tailIH : FactoredDecBoundedIH (F := F) interp transform limit (second :: rest)) :
    FactoredDecBoundedIH (F := F) interp transform limit (first :: second :: rest) := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result clockBound sourceRun invariant compiled envInv notTypeError generation future bounded
  generalize firstCompiled : compileDecs trace n start env gen [first] = firstTuple
  obtain ⟨n1, next1, env1, gen1, code1⟩ := firstTuple
  generalize tailCompiled : compileDecs trace n1 next1 (extendEnv env1 env) gen1 (second :: rest) = tailTuple
  obtain ⟨n2, next2, env2, gen2, code2⟩ := tailTuple
  have wholeCompiled : compileDecs trace n start env gen (first :: second :: rest) =
      (n2, next2, extendEnv env2 env1, gen2, code1 ++ code2) := by
    simp [compileDecs, firstCompiled, tailCompiled]
  have compiledEq := compiled.symm.trans wholeCompiled
  simp only [Prod.mk.injEq] at compiledEq
  obtain ⟨_, nextEq, envEq, genEq, codeEq⟩ := compiledEq
  subst next
  subst nextEnv
  subst nextGen
  subst flatDecs
  have validGen := invariantEnvGenInv interp transform gen genv start finish other source flat invariant
  have validFirst := (compileDecs_envGenInv trace n start env gen [first] n1 next1 env1 gen1 code1
    firstCompiled validGen).1
  have validFinal := (compileDecs_envGenInv trace n1 next1 (extendEnv env1 env) gen1 (second :: rest)
    n2 next2 env2 gen2 code2 tailCompiled validFirst).1
  have previous := compileDecs_idxPrev trace n1 next1 (extendEnv env1 env) gen1 (second :: rest)
    n2 next2 env2 gen2 code2 tailCompiled
  have firstBound := idxPrev_trans next1 next2 finish ⟨previous, bounded⟩
  have firstFuture := compileDecs_futureRel interp trace n1 next1 (extendEnv env1 env) gen1
    (second :: rest) n2 next2 env2 gen2 code2 source.evalState ⟨tailCompiled, future, validFirst⟩
  generalize firstRun : EvaluateHOL.evaluateDecs source sourceEnv [first] = firstResult
  obtain ⟨middle, firstResult⟩ := firstResult
  have clockFix : EvaluateHOL.fixClock source (EvaluateHOL.evaluateDecs source sourceEnv [first]) =
      EvaluateHOL.evaluateDecs source sourceEnv [first] :=
    (EvaluateHOL.fixClockEvaluate source sourceEnv [] [first]).2
  cases firstResult with
  | err error =>
    have fixed : EvaluateHOL.fixClock source (middle, (Result.err error : Result (SemEnv Value) Value)) =
        (middle, .err error) := by
      rw [← firstRun]
      exact clockFix
    have sourceEq : sourceLast = middle ∧ result = .err error := by
      have h := sourceRun
      simp only [EvaluateHOL.evaluateDecs, firstRun, fixed] at h
      exact Prod.mk.inj h.symm
    obtain ⟨lastEq, resultEq⟩ := sourceEq
    subst sourceLast
    subst result
    have firstCase := firstIH genv env env1 sourceEnv trace source middle flat start finish next1 other n n1
      gen gen1 code1 (.err error) clockBound firstRun invariant firstCompiled envInv notTypeError generation firstFuture firstBound
    exact factoredDecCase_append_error interp transform genv env1 env2 source middle flat finish next1 next2 other
      gen1 gen2 code1 code2 error firstCase previous bounded validFinal
  | val firstEnv =>
    have fixed : EvaluateHOL.fixClock source (middle, (Result.val firstEnv : Result (SemEnv Value) Value)) =
        (middle, .val firstEnv) := by
      rw [← firstRun]
      exact clockFix
    generalize tailRun : EvaluateHOL.evaluateDecs middle (extendDecEnv firstEnv sourceEnv) (second :: rest) = tailResult
    obtain ⟨last, tailResult⟩ := tailResult
    have sourceEq : sourceLast = last ∧ result = combineDecResult firstEnv tailResult := by
      have h := sourceRun
      simp only [EvaluateHOL.evaluateDecs, firstRun, fixed, tailRun] at h
      exact Prod.mk.inj h.symm
    obtain ⟨lastEq, resultEq⟩ := sourceEq
    subst sourceLast
    subst result
    have firstCase := firstIH genv env env1 sourceEnv trace source middle flat start finish next1 other n n1
      gen gen1 code1 (.val firstEnv) clockBound firstRun invariant firstCompiled envInv (by simp) generation firstFuture firstBound
    have tailSafe : tailResult ≠ .err (.abort .typeError) := by
      cases tailResult with
      | val resultEnv => simp
      | err error => simpa [combineDecResult] using notTypeError
    apply factoredDecCase_append_success interp transform genv env env1 env2 sourceEnv firstEnv source middle last flat
      finish next1 next2 other gen1 gen2 code1 code2 tailResult envInv future firstCase
    intro midGenv midFlat midInvariant midInv midGeneration midFuture
    exact tailIH midGenv (extendEnv env1 env) env2 (extendDecEnv firstEnv sourceEnv) trace middle last midFlat
      next1 finish next2 other n1 n2 gen1 gen2 code2 tailResult
      (Nat.le_trans (EvaluateHOL.evaluateDecsClockFull source middle sourceEnv [first] _ firstRun) clockBound) tailRun midInvariant tailCompiled midInv tailSafe
      midGeneration midFuture bounded

/-- A declaration list has a bounded simulation when each singleton does. -/
theorem factoredDecBoundedIH_list {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (decs : List Dec)
    (singletons : ∀ dec, dec ∈ decs → FactoredDecBoundedIH (F := F) interp transform limit [dec]) :
    FactoredDecBoundedIH (F := F) interp transform limit decs := by
  induction decs with
  | nil => exact factoredDecBoundedIH_empty interp transform limit
  | cons first rest ih =>
    cases rest with
    | nil => exact singletons first (by simp)
    | cons second tail =>
      apply factoredDecBoundedIH_cons interp transform limit first second tail
      · exact singletons first (by simp)
      · apply ih
        intro dec member
        exact singletons dec (by simp [member])

end Flapjack.Compiler.Backend.SourceToFlat
