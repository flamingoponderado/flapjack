import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateModule
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateException
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDatatype

/-! Local declaration simulation over the preliminary factored relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A successful local block supplies its bindings to the body, while only
the body's environment escapes. The body premise is the declaration
induction hypothesis, including its ordinary invariant and oracle premises. -/
theorem factoredDecCase_local_success {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (baseMap localMap bodyMap : Environment)
    (baseEnv localEnv : SemEnv Value) (source middle last : State F) (flat : FlatSem.State C F)
    (finish localNext bodyNext : NextIndices) (other : Set (Nat × IndexKind))
    (localGen bodyGen : EnvironmentGenerationStore) (localCode bodyCode : List FlatLang.Exp)
    (bodyResult : Result (SemEnv Value) Value)
    (baseInv : GlobalEnvInv genv baseMap (fun _ => False) baseEnv)
    (future : envGenFutureRel interp bodyGen source.evalState)
    (localCase : FactoredDecCase interp transform genv source middle flat finish localNext other localGen
      localMap localCode (.val localEnv))
    (bodyIH : ∀ midGenv midFlat,
      factoredInvariant interp transform localGen midGenv (localNext, finish, other) middle midFlat →
      GlobalEnvInv midGenv (extendEnv localMap baseMap) (fun _ => False) (extendDecEnv localEnv baseEnv) →
      envGenRel localGen middle.evalState → envGenFutureRel interp bodyGen middle.evalState →
      FactoredDecCase interp transform midGenv middle last midFlat finish bodyNext other bodyGen bodyMap
        bodyCode bodyResult) :
    FactoredDecCase interp transform genv source last flat finish bodyNext other bodyGen bodyMap
      (localCode ++ bodyCode) bodyResult := by
  obtain ⟨midFlat, midGenv, localError, localRun, _, localPost, localSuccess, _⟩ := localCase
  obtain ⟨localInvariant, localForward, localGrowth⟩ := localPost trivial
  obtain ⟨localNone, localDomain, localGeneration, localEnvInv⟩ := localSuccess localEnv rfl
  subst localError
  have baseMid := globalEnvInv_growth genv midGenv localGrowth baseMap (fun _ => False) baseEnv baseInv
  have combinedInv := globalEnvInv_append_factored midGenv localMap baseMap localEnv baseEnv
    localDomain localEnvInv baseMid
  have futureMid := envGenFutureRel_forward interp bodyGen source.evalState middle.evalState future localForward
  obtain ⟨lastFlat, lastGenv, bodyError, bodyRun, lastStates, bodyPost, bodySuccess, bodyErrors⟩ :=
    bodyIH midGenv midFlat localInvariant combinedInv localGeneration futureMid
  have flatRun : FlatSem.evaluateDecs flat (localCode ++ bodyCode) = (lastFlat, bodyError) := by
    rw [FlatSem.evaluateDecs_append, localRun]
    exact bodyRun
  refine ⟨lastFlat, lastGenv, bodyError, flatRun, lastStates, ?_, bodySuccess, bodyErrors⟩
  intro notAbort
  obtain ⟨finalInvariant, bodyForward, bodyGrowth⟩ := bodyPost notAbort
  exact ⟨finalInvariant, oracForwardRel_trans interp _ _ _ ⟨localForward, bodyForward⟩,
    localGrowth.trans bodyGrowth⟩

/-- Changing the returned compiler environment is irrelevant when the source
declaration ended in an error. -/
theorem factoredDecCase_error_changeEnv {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (source last : State F) (flat : FlatSem.State C F)
    (finish next : NextIndices) (other : Set (Nat × IndexKind)) (gen : EnvironmentGenerationStore)
    (oldMap newMap : Environment) (code : List FlatLang.Exp) (error : ErrorResult Value)
    (old : FactoredDecCase interp transform genv source last flat finish next other gen oldMap code (.err error)) :
    FactoredDecCase interp transform genv source last flat finish next other gen newMap code (.err error) := by
  obtain ⟨finalFlat, finalGenv, flatError, run, states, post, _, errors⟩ := old
  refine ⟨finalFlat, finalGenv, flatError, run, states, post, ?_, errors⟩
  intro resultEnv impossible
  cases impossible

/-- Local declaration case: the compiler and source evaluator compose the
two blocks, retaining only the body's exported environment. -/
theorem factoredDecIH_dlocal {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (locals body : List Dec) (localIH : FactoredDecIH (F := F) interp transform locals)
    (bodyIH : FactoredDecIH (F := F) interp transform body) :
    FactoredDecIH (F := F) interp transform [.dlocal locals body] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  generalize localCompiled : compileDecs trace n start env gen locals = localTuple
  obtain ⟨n1, next1, env1, gen1, code1⟩ := localTuple
  generalize bodyCompiled : compileDecs trace n1 next1 (extendEnv env1 env) gen1 body = bodyTuple
  obtain ⟨n2, next2, env2, gen2, code2⟩ := bodyTuple
  have outerCompiled : compileDecs trace n start env gen [.dlocal locals body] =
      (n2, next2, env2, gen2, code1 ++ code2) := by
    simp [compileDecs, localCompiled, bodyCompiled]
  have compiledEq := compiled.symm.trans outerCompiled
  simp only [Prod.mk.injEq] at compiledEq
  obtain ⟨_, nextEq, envEq, genEq, codeEq⟩ := compiledEq
  subst next
  subst nextEnv
  subst nextGen
  subst flatDecs
  have invariantCopy := invariant
  obtain ⟨_, _, _, _, _, _, _, _, validGen, _⟩ := invariantCopy
  have validFirst := (compileDecs_envGenInv trace n start env gen locals n1 next1 env1 gen1 code1
    localCompiled validGen).1
  have validFinal := (compileDecs_envGenInv trace n1 next1 (extendEnv env1 env) gen1 body
    n2 next2 env2 gen2 code2 bodyCompiled validFirst).1
  have previous := compileDecs_idxPrev trace n1 next1 (extendEnv env1 env) gen1 body
    n2 next2 env2 gen2 code2 bodyCompiled
  have firstBound := idxPrev_trans next1 next2 finish ⟨previous, bounded⟩
  have firstFuture := compileDecs_futureRel interp trace n1 next1 (extendEnv env1 env) gen1 body
    n2 next2 env2 gen2 code2 source.evalState bodyCompiled future validFirst
  generalize localRun : EvaluateHOL.evaluateDecs source sourceEnv locals = localResult
  obtain ⟨middle, localResult⟩ := localResult
  have clockFix : EvaluateHOL.fixClock source (EvaluateHOL.evaluateDecs source sourceEnv locals) =
      EvaluateHOL.evaluateDecs source sourceEnv locals :=
    (EvaluateHOL.fixClockEvaluate source sourceEnv [] locals).2
  cases localResult with
  | err error =>
    have fixed : EvaluateHOL.fixClock source (middle, (Result.err error : Result (SemEnv Value) Value)) =
        (middle, .err error) := by
      rw [← localRun]
      exact clockFix
    have sourceEq : sourceLast = middle ∧ result = .err error := by
      have h := sourceRun
      simp only [EvaluateHOL.evaluateDecs, localRun, fixed] at h
      exact Prod.mk.inj h.symm
    obtain ⟨lastEq, resultEq⟩ := sourceEq
    subst sourceLast
    subst result
    have localCase := localIH genv env env1 sourceEnv trace source middle flat start finish next1 other n n1
      gen gen1 code1 (.err error) localRun invariant localCompiled envInv notTypeError generation firstFuture firstBound
    have combined := factoredDecCase_append_error interp transform genv env1 env2 source middle flat finish next1 next2
      other gen1 gen2 code1 code2 error localCase previous bounded validFinal
    exact factoredDecCase_error_changeEnv interp transform genv source middle flat finish next2 other gen2
      (extendEnv env2 env1) env2 (code1 ++ code2) error combined
  | val localEnv =>
    have fixed : EvaluateHOL.fixClock source (middle, (Result.val localEnv : Result (SemEnv Value) Value)) =
        (middle, .val localEnv) := by
      rw [← localRun]
      exact clockFix
    have bodyRun : EvaluateHOL.evaluateDecs middle (extendDecEnv localEnv sourceEnv) body = (sourceLast, result) := by
      have h := sourceRun
      simpa only [EvaluateHOL.evaluateDecs, localRun, fixed] using h
    have localCase := localIH genv env env1 sourceEnv trace source middle flat start finish next1 other n n1
      gen gen1 code1 (.val localEnv) localRun invariant localCompiled envInv (by simp) generation firstFuture firstBound
    apply factoredDecCase_local_success interp transform genv env env1 env2 sourceEnv localEnv source middle
      sourceLast flat finish next1 next2 other gen1 gen2 code1 code2 result envInv future localCase
    intro midGenv midFlat midInvariant midInv midGeneration midFuture
    exact bodyIH midGenv (extendEnv env1 env) env2 (extendDecEnv localEnv sourceEnv) trace middle sourceLast midFlat
      next1 finish next2 other n1 n2 gen1 gen2 code2 result bodyRun midInvariant bodyCompiled midInv notTypeError
      midGeneration midFuture bounded

/-- Partial proof coverage recursively extended through modules and local
blocks. This is proof bookkeeping and does not constrain CakeML programs. -/
inductive FactoredScopedDec : Dec → Prop where
  | basic (dec : Dec) : FactoredDecSupported dec → FactoredScopedDec dec
  | exception_ (location : Flapjack.Misc.Location.Locs) (name : ConN) (types : List AstT) :
      FactoredScopedDec (.dexn location name types)
  | datatype_ (location : Flapjack.Misc.Location.Locs) (types : TypeDef) :
      FactoredScopedDec (.dtype location types)
  | module_ (moduleName : ModN) (decs : List Dec) :
      (∀ dec, dec ∈ decs → FactoredScopedDec dec) → FactoredScopedDec (.dmod moduleName decs)
  | local_ (locals body : List Dec) :
      (∀ dec, dec ∈ locals → FactoredScopedDec dec) →
      (∀ dec, dec ∈ body → FactoredScopedDec dec) → FactoredScopedDec (.dlocal locals body)

/-- Covered nested module and local declarations satisfy the factored
singleton simulation. The factored relations still need HOL review. -/
theorem factoredDecIH_scoped {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (dec : Dec) (covered : FactoredScopedDec dec) : FactoredDecIH (F := F) interp transform [dec] := by
  induction covered with
  | basic dec supported =>
    apply factoredDecIH_supported_list interp transform [dec]
    intro item member
    simp only [List.mem_singleton] at member
    subst item
    exact supported
  | exception_ location name types => exact factoredDecIH_dexn interp transform location name types
  | datatype_ location types => exact factoredDecIH_dtype interp transform location types
  | module_ moduleName decs _ ih =>
    apply factoredDecIH_dmod interp transform moduleName decs
    apply factoredDecIH_list interp transform decs
    exact ih
  | local_ locals body _ _ localIH bodyIH =>
    apply factoredDecIH_dlocal interp transform locals body
    · apply factoredDecIH_list interp transform locals
      exact localIH
    · apply factoredDecIH_list interp transform body
      exact bodyIH

/-- Any list built from the covered base forms, modules and local blocks
satisfies the factored declaration simulation. -/
theorem factoredDecIH_scoped_list {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (decs : List Dec) (covered : ∀ dec, dec ∈ decs → FactoredScopedDec dec) :
    FactoredDecIH (F := F) interp transform decs := by
  apply factoredDecIH_list interp transform decs
  intro dec member
  exact factoredDecIH_scoped interp transform dec (covered dec member)

end Flapjack.Compiler.Backend.SourceToFlat
