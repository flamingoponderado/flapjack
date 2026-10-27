import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateEmptyDeclarations
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EnvironmentDomain
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDletrec
import Flapjack.EvaluateHOL.ClockFull

/-! Sequential declaration composition over the preliminary factored
source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- The declaration induction hypothesis over the current factored
relations. This is not yet the reviewed HOL compiler theorem. -/
def FactoredDecIH {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (decs : List Dec) : Prop :=
  ∀ (genv : GlobalEnv) (env nextEnv : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (source sourceLast : State F) (flat : FlatSem.State C F) (start finish next : NextIndices)
    (other : Set (Nat × IndexKind)) (n n' : Nat) (gen nextGen : EnvironmentGenerationStore)
    (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value),
    EvaluateHOL.evaluateDecs source sourceEnv decs = (sourceLast, result) →
    factoredInvariant interp transform gen genv (start, finish, other) source flat →
    compileDecs trace n start env gen decs = (n', next, nextEnv, nextGen, flatDecs) →
    GlobalEnvInv genv env (fun _ => False) sourceEnv →
    result ≠ .err (.abort .typeError) → envGenRel gen source.evalState →
    envGenFutureRel interp nextGen source.evalState → idxPrev next finish →
    FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen nextEnv flatDecs result

/-- Empty declaration lists satisfy the factored induction hypothesis. -/
theorem factoredDecIH_empty {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) :
    FactoredDecIH (F := F) interp transform [] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  exact evaluateDecs_empty_case interp transform genv env nextEnv sourceEnv trace source sourceLast flat
    start finish next other n n' gen nextGen flatDecs result sourceRun invariant compiled envInv notTypeError
    generation future bounded

/-- Type-abbreviation declarations satisfy the factored induction hypothesis. -/
theorem factoredDecIH_dtabbrev {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (typeVars : List TvarN) (name : TypeN) (typ : AstT) :
    FactoredDecIH (F := F) interp transform [.dtabbrev location typeVars name typ] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  exact evaluateDtabbrev_case interp transform genv env nextEnv sourceEnv trace source sourceLast flat
    start finish next other n n' gen nextGen location typeVars name typ flatDecs result sourceRun invariant compiled
    envInv notTypeError generation future bounded

/-- Recursive declarations satisfy the factored induction hypothesis. -/
theorem factoredDecIH_dletrec {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (funs : List (VarN × VarN × AstHOL.Exp)) :
    FactoredDecIH (F := F) interp transform [.dletrec location funs] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  exact evaluateDletrec_case_factored interp transform genv env nextEnv sourceEnv trace funs source sourceLast flat
    start finish next other n n' gen nextGen location flatDecs result sourceRun invariant compiled envInv
    notTypeError generation future bounded

/-- Environment declarations satisfy the factored induction hypothesis,
including the oracle and generation updates. -/
theorem factoredDecIH_denv {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (name : VarN) :
    FactoredDecIH (F := F) interp transform [.denv name] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
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

/-- Literal-initialized value declarations satisfy the factored induction
hypothesis for any source-safe pattern. -/
theorem factoredDecIH_dlet_literal {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (lit : Lit) :
    FactoredDecIH (F := F) interp transform [.dlet location pattern (.lit lit)] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  apply evaluateDlet_case_factored interp transform genv start finish next other source sourceLast flat sourceEnv
    trace n n' env nextEnv gen nextGen location pattern (.lit lit) flatDecs result sourceRun invariant compiled
    envInv notTypeError generation future bounded
  exact dletExpressionStep_literal interp transform genv start finish other source flat sourceEnv
    ((AstHOL.patBindings pattern).reverse ++ trace) env gen lit invariant generation

/-- Function-initialized value declarations satisfy the factored induction
hypothesis for any source-safe pattern. -/
theorem factoredDecIH_dlet_function {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (name : VarN) (body : AstHOL.Exp) :
    FactoredDecIH (F := F) interp transform [.dlet location pattern (.fn name body)] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  apply evaluateDlet_case_factored interp transform genv start finish next other source sourceLast flat sourceEnv
    trace n n' env nextEnv gen nextGen location pattern (.fn name body) flatDecs result sourceRun invariant compiled
    envInv notTypeError generation future bounded
  exact dletExpressionStep_function interp transform genv start finish other source flat sourceEnv
    ((AstHOL.patBindings pattern).reverse ++ trace) env gen name body envInv invariant generation

/-- Global-variable-initialized value declarations satisfy the factored
induction hypothesis; source safety supplies the variable lookup. -/
theorem factoredDecIH_dlet_variable {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (id : Ident ModN VarN) :
    FactoredDecIH (F := F) interp transform [.dlet location pattern (.var id)] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation _future bounded
  apply DletOutcomeAdvanced.toFactoredDecCase interp transform genv start finish next other source sourceLast flat
    sourceEnv trace n n' env nextEnv gen nextGen location pattern (.var id) flatDecs result sourceRun compiled
  exact evaluateDlet_variable_advanced interp transform genv start finish next other source sourceLast flat
    sourceEnv trace n n' env nextEnv gen nextGen location pattern id flatDecs result compiled bounded sourceRun
    notTypeError envInv invariant generation

/-- Expression forms whose factored simulation is currently available in an
empty local environment, including nested source annotations. -/
inductive FactoredSimpleExpression : AstHOL.Exp → Prop where
  | literal (lit : Lit) : FactoredSimpleExpression (.lit lit)
  | function (name : VarN) (body : AstHOL.Exp) : FactoredSimpleExpression (.fn name body)
  | variable (id : Ident ModN VarN) : FactoredSimpleExpression (.var id)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : FactoredSimpleExpression expr →
      FactoredSimpleExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : FactoredSimpleExpression expr →
      FactoredSimpleExpression (.lannot expr loc)

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

/-- Simple expressions and their annotations satisfy the factored expression
step under the source non-type-error premise. -/
theorem factoredSimpleExpression_step {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (env : Environment) (gen : EnvironmentGenerationStore) (expr : AstHOL.Exp)
    (supported : FactoredSimpleExpression expr)
    (envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source sourceEnv [expr] ≠ (last, .err (.abort .typeError))) :
    DletExpressionStep interp transform genv start finish other source flat sourceEnv trace env gen expr := by
  induction supported with
  | literal lit =>
    exact dletExpressionStep_literal interp transform genv start finish other source flat
      sourceEnv trace env gen lit invariant generation
  | function name body =>
    exact dletExpressionStep_function interp transform genv start finish other source flat
      sourceEnv trace env gen name body envInv invariant generation
  | «variable» id =>
    cases lookup : nsLookup sourceEnv.v id with
    | some value =>
      exact dletExpressionStep_global interp transform genv start finish other source flat sourceEnv
        trace env gen id value lookup envInv invariant generation
    | none =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.var id] = (source, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, lookup, EvaluateHOL.typeError]
      exact False.elim (safe source bad)
  | tannot expr typ _ ih =>
    apply dletExpressionStep_tannot interp transform genv start finish other source flat sourceEnv trace env gen expr typ
    apply ih
    intro last bad
    apply safe last
    simpa [EvaluateHOL.evaluate] using bad
  | lannot expr loc _ ih =>
    apply dletExpressionStep_lannot interp transform genv start finish other source flat sourceEnv trace env gen expr loc
    apply ih
    intro last bad
    apply safe last
    cases loc
    simpa [EvaluateHOL.evaluate] using bad

/-- Value declarations with a simple, possibly annotated initializer satisfy
the factored declaration induction hypothesis. -/
theorem factoredDecIH_dlet_simple {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (supported : FactoredSimpleExpression expr) :
    FactoredDecIH (F := F) interp transform [.dlet location pattern expr] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  have safe : ∀ last, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply notTypeError
    exact congrArg Prod.snd (sourceRun.symm.trans bad)
  apply evaluateDlet_case_factored interp transform genv start finish next other source sourceLast flat sourceEnv
    trace n n' env nextEnv gen nextGen location pattern expr flatDecs result sourceRun invariant compiled
    envInv notTypeError generation future bounded
  exact factoredSimpleExpression_step interp transform genv start finish other source flat sourceEnv
    ((AstHOL.patBindings pattern).reverse ++ trace) env gen expr supported envInv invariant generation
    (dlet_expression_safe source sourceEnv location pattern expr safe)

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
    firstDomain firstEnvInv baseMid
  have futureMid := envGenFutureRel_forward interp lastGen source.evalState middle.evalState future firstForward
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
          tailDomain tailEnvInv firstFinal⟩
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
      have shrunk := factoredInvariant_shrink interp transform firstGen finalGenv firstNext lastNext finish
        other last finalFlat invariant previous bounded
      exact ⟨factoredInvariant_changeGen interp transform firstGen lastGen finalGenv
        (lastNext, finish, other) last finalFlat shrunk lastGenValid, forward, growth⟩
  · intro resultEnv impossible
    cases impossible
  · intro error' same
    cases same
    exact ⟨flatErr, rfl, related⟩

/-- The declaration-list induction step, assuming the first declaration and
the remaining declarations satisfy the factored induction hypothesis. -/
theorem factoredDecIH_cons {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (first second : Dec) (rest : List Dec)
    (firstIH : FactoredDecIH (F := F) interp transform [first])
    (tailIH : FactoredDecIH (F := F) interp transform (second :: rest)) :
    FactoredDecIH (F := F) interp transform (first :: second :: rest) := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
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
  have invariantCopy := invariant
  obtain ⟨_, _, _, _, _, _, _, _, validGen, _⟩ := invariantCopy
  have validFirst := (compileDecs_envGenInv trace n start env gen [first] n1 next1 env1 gen1 code1
    firstCompiled validGen).1
  have validFinal := (compileDecs_envGenInv trace n1 next1 (extendEnv env1 env) gen1 (second :: rest)
    n2 next2 env2 gen2 code2 tailCompiled validFirst).1
  have previous := compileDecs_idxPrev trace n1 next1 (extendEnv env1 env) gen1 (second :: rest)
    n2 next2 env2 gen2 code2 tailCompiled
  have firstBound := idxPrev_trans next1 next2 finish ⟨previous, bounded⟩
  have firstFuture := compileDecs_futureRel interp trace n1 next1 (extendEnv env1 env) gen1
    (second :: rest) n2 next2 env2 gen2 code2 source.evalState tailCompiled future validFirst
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
      gen gen1 code1 (.err error) firstRun invariant firstCompiled envInv notTypeError generation firstFuture firstBound
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
      gen gen1 code1 (.val firstEnv) firstRun invariant firstCompiled envInv (by simp) generation firstFuture firstBound
    have tailSafe : tailResult ≠ .err (.abort .typeError) := by
      cases tailResult with
      | val resultEnv => simp
      | err error => simpa [combineDecResult] using notTypeError
    apply factoredDecCase_append_success interp transform genv env env1 env2 sourceEnv firstEnv source middle last flat
      finish next1 next2 other gen1 gen2 code1 code2 tailResult envInv future firstCase
    intro midGenv midFlat midInvariant midInv midGeneration midFuture
    exact tailIH midGenv (extendEnv env1 env) env2 (extendDecEnv firstEnv sourceEnv) trace middle last midFlat
      next1 finish next2 other n1 n2 gen1 gen2 code2 tailResult tailRun midInvariant tailCompiled midInv tailSafe
      midGeneration midFuture bounded

/-- A declaration list satisfies the factored simulation whenever each of
its singleton declarations satisfies the factored induction hypothesis. -/
theorem factoredDecIH_list {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (decs : List Dec)
    (singletons : ∀ dec, dec ∈ decs → FactoredDecIH (F := F) interp transform [dec]) :
    FactoredDecIH (F := F) interp transform decs := by
  induction decs with
  | nil => exact factoredDecIH_empty interp transform
  | cons first rest ih =>
    cases rest with
    | nil => exact singletons first (by simp)
    | cons second tail =>
      apply factoredDecIH_cons interp transform first second tail
      · exact singletons first (by simp)
      · apply ih
        intro dec member
        exact singletons dec (by simp [member])

/-- Declaration forms for which the factored singleton simulation has been
proved. This predicate tracks a partial proof, not a language restriction. -/
inductive FactoredDecSupported : Dec → Prop where
  | tabbrev (location : Flapjack.Misc.Location.Locs) (vars : List TvarN) (name : TypeN) (typ : AstT) :
      FactoredDecSupported (.dtabbrev location vars name typ)
  | letrec (location : Flapjack.Misc.Location.Locs) (funs : List (VarN × VarN × AstHOL.Exp)) :
      FactoredDecSupported (.dletrec location funs)
  | denv (name : VarN) : FactoredDecSupported (.denv name)
  | simple (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      FactoredSimpleExpression expr → FactoredDecSupported (.dlet location pattern expr)

/-- Every finite list of the currently proved declaration forms satisfies the
factored declaration simulation. Other forms and correspondence of the
factored relations with HOL remain open. -/
theorem factoredDecIH_supported_list {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (decs : List Dec)
    (supported : ∀ dec, dec ∈ decs → FactoredDecSupported dec) :
    FactoredDecIH (F := F) interp transform decs := by
  apply factoredDecIH_list interp transform decs
  intro dec member
  cases supported dec member with
  | tabbrev location vars name typ => exact factoredDecIH_dtabbrev interp transform location vars name typ
  | letrec location funs => exact factoredDecIH_dletrec interp transform location funs
  | denv name => exact factoredDecIH_denv interp transform name
  | simple location pattern expr expression => exact factoredDecIH_dlet_simple interp transform location pattern expr expression

end Flapjack.Compiler.Backend.SourceToFlat
