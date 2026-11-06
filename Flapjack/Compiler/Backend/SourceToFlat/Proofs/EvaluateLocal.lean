import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateModule
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateException
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDatatype
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingConstructors
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalArray
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedArrayTree
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.Initialization
import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics
import Flapjack.SemanticsProps.Clock

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
    ⟨localDomain, localEnvInv, baseMid⟩
  have futureMid := envGenFutureRel_forward interp bodyGen source.evalState middle.evalState ⟨future, localForward⟩
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

/- Bounded versions retain the source clock bound across nested declarations. -/
theorem factoredDecBoundedIH_dmod {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (moduleName : ModN) (decs : List Dec) (innerIH : FactoredDecBoundedIH (F := F) interp transform limit decs) :
    FactoredDecBoundedIH (F := F) interp transform limit [.dmod moduleName decs] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result clockBound sourceRun invariant compiled envInv notTypeError generation future bounded
  generalize innerCompiled : compileDecs (moduleName :: trace) n start env gen decs = innerTuple
  obtain ⟨innerN, innerNext, innerEnv, innerGen, innerCode⟩ := innerTuple
  have outerCompiled : compileDecs trace n start env gen [.dmod moduleName decs] =
      (innerN, innerNext, liftEnv moduleName innerEnv, innerGen, innerCode) := by
    simp [compileDecs, innerCompiled]
  have compEq := compiled.symm.trans outerCompiled
  simp only [Prod.mk.injEq] at compEq
  obtain ⟨_, nextEq, envEq, genEq, codeEq⟩ := compEq
  subst next
  subst nextEnv
  subst nextGen
  subst flatDecs
  generalize innerRun : EvaluateHOL.evaluateDecs source sourceEnv decs = innerPair
  obtain ⟨innerLast, innerResult⟩ := innerPair
  have resultEq : sourceLast = innerLast ∧ result =
      (match innerResult with
       | .val inner => .val ⟨nsLift moduleName inner.v, nsLift moduleName inner.c⟩
       | .err error => .err error) := by
    have h := sourceRun
    simp only [EvaluateHOL.evaluateDecs, innerRun] at h
    cases innerResult <;> simp_all
  obtain ⟨lastEq, outEq⟩ := resultEq
  subst sourceLast
  subst result
  have innerSafe : innerResult ≠ .err (.abort .typeError) := by
    cases innerResult with
    | val resultEnv => simp
    | err error => simpa using notTypeError
  have inner := innerIH genv env innerEnv sourceEnv (moduleName :: trace) source innerLast flat start finish
    innerNext other n innerN gen innerGen innerCode innerResult clockBound innerRun invariant innerCompiled envInv innerSafe
    generation future bounded
  cases innerResult <;>
    exact factoredDecCase_liftModule interp transform genv source innerLast flat finish innerNext other innerGen
      innerEnv moduleName innerCode _ inner

theorem factoredDecBoundedIH_dlocal {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (locals body : List Dec) (localIH : FactoredDecBoundedIH (F := F) interp transform limit locals)
    (bodyIH : FactoredDecBoundedIH (F := F) interp transform limit body) :
    FactoredDecBoundedIH (F := F) interp transform limit [.dlocal locals body] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result clockBound sourceRun invariant compiled envInv notTypeError generation future bounded
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
    n2 next2 env2 gen2 code2 source.evalState ⟨bodyCompiled, future, validFirst⟩
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
      gen gen1 code1 (.err error) clockBound localRun invariant localCompiled envInv notTypeError generation firstFuture firstBound
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
      gen gen1 code1 (.val localEnv) clockBound localRun invariant localCompiled envInv (by simp) generation firstFuture firstBound
    apply factoredDecCase_local_success interp transform genv env env1 env2 sourceEnv localEnv source middle
      sourceLast flat finish next1 next2 other gen1 gen2 code1 code2 result envInv future localCase
    intro midGenv midFlat midInvariant midInv midGeneration midFuture
    exact bodyIH midGenv (extendEnv env1 env) env2 (extendDecEnv localEnv sourceEnv) trace middle sourceLast midFlat
      next1 finish next2 other n1 n2 gen1 gen2 code2 result
      (Nat.le_trans (EvaluateHOL.evaluateDecsClockFull source middle sourceEnv locals _ localRun) clockBound) bodyRun midInvariant bodyCompiled midInv notTypeError
      midGeneration midFuture bounded

/-- Every singleton declaration has a bounded simulation, by structural
induction on the source declaration and its nested declaration lists. -/
theorem factoredDecBoundedIH_singleton {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (smallerExprs : ∀ n, n < limit → ∀ expr, LocalEnvBoundedIH (F := F) interp transform n expr)
    (smallerDecs : ∀ n, n < limit → ∀ decs, FactoredDecBoundedIH (F := F) interp transform n decs)
    (dec : Dec) : FactoredDecBoundedIH (F := F) interp transform limit [dec] := by
  cases dec with
  | dtabbrev location vars name typ =>
    exact factoredDecBoundedIH_dtabbrev interp transform limit location vars name typ
  | dletrec location funs =>
    exact factoredDecBoundedIH_dletrec interp transform limit location funs
  | denv name =>
    exact factoredDecBoundedIH_denv interp transform limit name
  | dexn location name types =>
    exact factoredDecBoundedIH_dexn interp transform limit location name types
  | dtype location types =>
    exact factoredDecBoundedIH_dtype interp transform limit location types
  | dlet location pattern expr =>
    apply factoredDecBoundedIH_dlet_expression interp transform limit location pattern expr
    exact localEnvBounded_arrayTree_of_smaller interp transform limit smallerExprs smallerDecs expr
  | dmod moduleName decs =>
    apply factoredDecBoundedIH_dmod interp transform limit moduleName decs
    apply factoredDecBoundedIH_list interp transform limit decs
    intro child member
    exact factoredDecBoundedIH_singleton interp transform limit smallerExprs smallerDecs child
  | dlocal locals body =>
    apply factoredDecBoundedIH_dlocal interp transform limit locals body
    · apply factoredDecBoundedIH_list interp transform limit locals
      intro child member
      exact factoredDecBoundedIH_singleton interp transform limit smallerExprs smallerDecs child
    · apply factoredDecBoundedIH_list interp transform limit body
      intro child member
      exact factoredDecBoundedIH_singleton interp transform limit smallerExprs smallerDecs child
termination_by sizeOf dec
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem member
  all_goals omega

/-- Simultaneous expression and declaration simulation at every clock bound.
This closes the clock induction over the preliminary factored relations; it is
not yet a reviewed port of HOL's pass-correctness theorem. -/
theorem factoredAllBounded {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) :
    (∀ expr, LocalEnvBoundedIH (F := F) interp transform limit expr) ∧
    (∀ decs, FactoredDecBoundedIH (F := F) interp transform limit decs) := by
  induction limit using Nat.strong_induction_on with
  | h limit ih =>
    have smallerExprs : ∀ n, n < limit → ∀ expr, LocalEnvBoundedIH (F := F) interp transform n expr :=
      fun n lt => (ih n lt).1
    have smallerDecs : ∀ n, n < limit → ∀ decs, FactoredDecBoundedIH (F := F) interp transform n decs :=
      fun n lt => (ih n lt).2
    constructor
    · intro expr
      exact localEnvBounded_arrayTree_of_smaller interp transform limit smallerExprs smallerDecs expr
    · intro decs
      apply factoredDecBoundedIH_list interp transform limit decs
      intro dec _
      exact factoredDecBoundedIH_singleton interp transform limit smallerExprs smallerDecs dec

/-- Arbitrary source declaration lists satisfy the preliminary factored
simulation. This is not yet the reviewed HOL pass-correctness statement. -/
theorem factoredDecIH_all {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (decs : List Dec) : FactoredDecIH (F := F) interp transform decs := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen flatDecs result
  exact (factoredAllBounded (F := F) interp transform source.clock).2 decs genv env nextEnv sourceEnv trace
    source sourceLast flat start finish next other n n' gen nextGen flatDecs result (Nat.le_refl _)

namespace InitialEnv
/-- The canonical finite-map carrier used by the initial environment. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env

/-- The source's initial global-environment condition, with canonical finite maps. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "init_global_env_inv_def"
  (fmap_as_finite_support := [c, tys])]
def initGlobalEnvInv {α : Type} (genv : GlobalEnv) (compMap : Environment) (env : SemEnv α) : Prop :=
  env.v = nsEmpty ∧
    match env.c with
    | .bind entries modules => modules = [] ∧ ∀ entry ∈ entries,
        match nsLookup compMap.c (.short entry.1) with
        | none => False
        | some (cn, tyGroup) =>
          genv.c.lookup ((cn, tyGroup.map Prod.fst), entry.2.1) = some entry.2.2 ∧
          match tyGroup with
          | none => True
          | some (tyId, ctors) => genv.tys.lookup tyId = some ctors
end InitialEnv

private theorem constructorLookup_member {α : Type} (entries : List (ConN × α)) (name : ConN) (value : α)
    (found : entries.lookup name = some value) : (name, value) ∈ entries := by
  induction entries with
  | nil => simp at found
  | cons head tail ih =>
    obtain ⟨key, current⟩ := head
    by_cases same : name = key
    · subst key
      simp at found
      subst current
      simp
    · have different : (name == key) = false := by
        change decide (name = key) = false
        simp [same]
      simp only [List.lookup_cons, different] at found
      exact List.mem_cons_of_mem _ (ih found)

/-- The initialization condition supplies the global environment invariant. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "init_global_env_inv_imp"
  (fmap_as_finite_support := [c, tys])]
theorem initGlobalEnvInv_imp (genv : GlobalEnv) (compMap : Environment) (env : SemEnv Value)
    (initial : InitialEnv.initGlobalEnvInv genv compMap env) :
    GlobalEnvInv genv compMap (fun _ => False) env := by
  obtain ⟨emptyValues, constructors⟩ := initial
  cases envC : env.c with
  | bind entries modules =>
    rw [envC] at constructors
    obtain ⟨rfl, entriesValid⟩ := constructors
    apply GlobalEnvInv.intro
    · intro id value _ found
      rw [emptyValues] at found
      cases id <;> simp [nsEmpty, nsLookup] at found
    · intro id arity stamp found
      rw [envC] at found
      cases id with
      | long module id => simp [nsLookup] at found
      | short name =>
        have member := constructorLookup_member entries name (arity, stamp) (by simpa [nsLookup] using found)
        have item := entriesValid (name, arity, stamp) member
        cases selected : nsLookup compMap.c (.short name) with
        | none => simp [selected] at item
        | some pair =>
          rcases pair with ⟨cn, group⟩
          simp only [selected] at item
          refine ⟨cn, group, rfl, item.1, ?_⟩
          intro ty ctors eq
          subst group
          exact item.2

namespace EnvAllRelPort

/-- Roundtrip for the global carrier's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env :=
  GlobalEnv.holFmapAsFiniteSupportWitness env

end EnvAllRelPort

/-- Combined local and global environment relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_all_rel"
  (fmap_as_finite_support := [c, tys])]
def FactoredEnvAllRel (genv : GlobalEnv) (compMap : Environment) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN) : Prop :=
  ∃ (baseEnv : SemEnv Value) (sourceLocal : Namespace ModN VarN Value) (bindings : List (VarN × Value)),
    sourceEnv = { baseEnv with v := nsAppend sourceLocal baseEnv.v } ∧
    sourceLocal = alistToNs bindings ∧ bindings.map Prod.fst = locals ∧
    GlobalEnvInv genv compMap (fun name => name ∈ locals) baseEnv ∧ EnvRel genv sourceLocal flatEnv.v

/-- The combined environment relation exposes its original case structure. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_all_rel_cases"
  (fmap_as_finite_support := [c, tys])]
theorem factoredEnvAllRel_source_cases (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN) :
    FactoredEnvAllRel genv compMap sourceEnv flatEnv locals ↔
      ∃ sourceLocal baseEnv flatValues,
        sourceEnv = { baseEnv with v := nsAppend sourceLocal baseEnv.v } ∧
        flatEnv = ⟨flatValues⟩ ∧
        (∃ bindings, sourceLocal = alistToNs bindings ∧ bindings.map Prod.fst = locals) ∧
        GlobalEnvInv genv compMap (fun name => name ∈ locals) baseEnv ∧
        EnvRel genv sourceLocal flatValues := by
  constructor
  · rintro ⟨base, sourceLocal, bindings, sourceEq, localEq, names, globals, localsRel⟩
    exact ⟨sourceLocal, base, flatEnv.v, sourceEq, by cases flatEnv; rfl,
      ⟨bindings, localEq, names⟩, globals, localsRel⟩
  · rintro ⟨sourceLocal, base, values, sourceEq, rfl, ⟨bindings, localEq, names⟩, globals, localsRel⟩
    exact ⟨base, sourceLocal, bindings, sourceEq, localEq, names, globals, localsRel⟩

/-- The factored combined environment relation determines the flat local
names. -/
theorem factoredEnvAllRel_names (genv : GlobalEnv) (compMap : Environment) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN)
    (related : FactoredEnvAllRel genv compMap sourceEnv flatEnv locals) :
    locals = flatEnv.v.map Prod.fst := by
  obtain ⟨_, _, bindings, _, localEq, names, _, localRel⟩ := related
  rw [localEq] at localRel
  have pairs := (envRel_alist_iff genv bindings flatEnv.v).mp localRel
  have namesOfPairs : ∀ (xs : List (VarN × Value)) (ys : List (VarN × FlatSem.Value)),
      List.Forall₂ (fun a b => a.1 = b.1 ∧ ValueRel genv a.2 b.2) xs ys →
      xs.map Prod.fst = ys.map Prod.fst := by
    intro xs ys pairs
    induction pairs with
    | nil => rfl
    | cons head tail ih =>
      simp only [List.map_cons]
      rw [head.1, ih]
  exact names.symm.trans (namesOfPairs bindings flatEnv.v pairs)

/-- Declaration-list result in existential form, over the preliminary
factored relations. -/
theorem factoredCompileDeclarations {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (decs : List Dec) (genv : GlobalEnv) (env nextEnv : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (source sourceLast : State F) (flat : FlatSem.State C F) (start finish next : NextIndices)
    (other : Set (Nat × IndexKind)) (n n' : Nat) (gen nextGen : EnvironmentGenerationStore)
    (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value)
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv decs = (sourceLast, result))
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (compiled : compileDecs trace n start env gen decs = (n', next, nextEnv, nextGen, flatDecs))
    (envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv)
    (safe : result ≠ .err (.abort .typeError)) (generation : envGenRel gen source.evalState)
    (future : envGenFutureRel interp nextGen source.evalState) (bounded : idxPrev next finish) :
    ∃ finalFlat nextGenv flatError,
      FlatSem.evaluateDecs flat flatDecs = (finalFlat, flatError) ∧ StateRel nextGenv sourceLast finalFlat ∧
      ((match result with | .err (.abort _) => False | _ => True) →
        factoredInvariant interp transform nextGen nextGenv (next, finish, other) sourceLast finalFlat ∧
        oracForwardRel interp source.evalState sourceLast.evalState ∧ GlobalGrowth genv nextGenv) ∧
      (∀ resultEnv, result = .val resultEnv → flatError = none ∧ EnvDomainEq nextEnv resultEnv ∧
        envGenRel nextGen sourceLast.evalState ∧ GlobalEnvInv nextGenv nextEnv (fun _ => False) resultEnv) ∧
      (∀ error, result = .err error → ∃ flatErr, flatError = some flatErr ∧
        ResultRel (fun _ (_ : SemEnv Value) (_ : Unit) => True) nextGenv (.err error) (.err flatErr)) := by
  have caseProof := factoredDecIH_all interp transform decs genv env nextEnv sourceEnv trace source sourceLast flat
    start finish next other n n' gen nextGen flatDecs result sourceRun invariant compiled envInv safe generation future bounded
  cases result with
  | val values => exact caseProof
  | err error => cases error <;> exact caseProof

/-- The original initialization conditions establish the preliminary
factored invariant immediately after allocation of the environment reference
and blank globals. The factored relations still require HOL correspondence
review. -/
theorem factoredInvariant_compileProg_initial {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (config : Config) (decs : List Dec) (source : State F) (flat : FlatSem.State C F)
    (n : Nat) (next : NextIndices) (outEnv : Environment) (outGen : EnvironmentGenerationStore)
    (body : List FlatLang.Exp)
    (compiled : compileDecs [] 1 { config.next with vidx := config.next.vidx + 1 } config.modEnv
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, outEnv, outGen, body))
    (startVar : config.next.vidx = 0) (initialIdx : idxPrev initGenvNext config.next)
    (emptyStore : config.envs = emptyConfig.envs) (initialEval : initEvalStateOk source.evalState)
    (steps : srcOracStepInvs interp transform source.evalState)
    (oracle : oracRel interp transform source.evalState flat.evalConfig)
    (oracleConfig : match srcOracNextCfg interp source.evalState with
      | none => True
      | some nextConfig => nextConfig = (compileProg config decs).1)
    (stamps : ∀ entry ∈ initGenvEntries, match entry.2 with
      | .typeStamp _ index => index < source.nextTypeStamp
      | .exnStamp index => index < source.nextExnStamp)
    (sourceRefs : source.refs = []) (clock : source.clock = flat.clock) (ffi : source.ffi = flat.ffi) :
    factoredInvariant interp transform ⟨0, config.envs.next, .ln⟩
      { initGenv with v := some (.loc true 0) ::
          List.replicate (next.vidx - config.next.vidx - 1) none }
      ({ config.next with vidx := config.next.vidx + 1 }, next, ∅) source
      { flat with globals := some (.loc true 0) :: List.replicate (next.vidx - config.next.vidx - 1) none,
                  refs := [.refv (.conv none [])] } := by
  have progress := compileDecs_idxPrev [] 1
    { config.next with vidx := config.next.vidx + 1 } config.modEnv
    ⟨0, config.envs.next, .ln⟩ decs n next outEnv outGen body compiled
  refine ⟨initGenv_constructorsOk, initGenv_typesOk, ?_, ?_, ?_, oracle, rfl, ?_, ?_, ?_⟩
  · apply StateRel.intro
    · simp
    · simp [sourceRefs]
    · exact clock
    · exact ffi
  · exact initGenv_idxRange_compileProg interp source.evalState source.nextTypeStamp source.nextExnStamp
      (next.vidx - config.next.vidx - 1) config decs n next outEnv outGen body compiled
      startVar initialIdx stamps oracleConfig
  · exact initEvalStateOk_srcOracInvs interp transform source.evalState _ config decs n next outEnv outGen
      body compiled emptyStore initialEval steps oracleConfig
  · simp [evalRefInv]
  · simp [envGenInv]
  · unfold finIdxMatch
    cases eq : srcOracNextCfg interp source.evalState with
    | none =>
      simp only [idxPrev] at progress
      simp [startVar] at progress ⊢
      omega
    | some nextConfig =>
      simp only [eq] at oracleConfig ⊢
      subst nextConfig
      simp only [compileProg, compiled]
      simp [startVar]
      simp only [idxPrev] at progress
      omega

/-- Compose whole-program prefix execution with the factored declaration
simulation. The prepared invariant and oracle conditions are explicit until
their derivation from the original whole-program precondition is ported. -/
theorem factoredCompileProg_prepared {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (config : Config) (decs : List Dec) (genv : GlobalEnv) (sourceEnv : SemEnv Value)
    (source sourceLast : State F) (flat : FlatSem.State C F)
    (n : Nat) (next : NextIndices) (outEnv : Environment) (outGen : EnvironmentGenerationStore)
    (body : List FlatLang.Exp) (result : Result (SemEnv Value) Value)
    (compiled : compileDecs [] 1 { config.next with vidx := config.next.vidx + 1 } config.modEnv
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, outEnv, outGen, body))
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv decs = (sourceLast, result))
    (globalsEmpty : flat.globals = []) (refsEmpty : flat.refs = [])
    (initialEnv : InitialEnv.initGlobalEnvInv genv config.modEnv sourceEnv)
    (invariant : factoredInvariant interp transform ⟨0, config.envs.next, .ln⟩ genv
      ({ config.next with vidx := config.next.vidx + 1 }, next, ∅) source
      { flat with globals := some (.loc true 0) :: List.replicate (next.vidx - config.next.vidx - 1) none,
                  refs := [.refv (.conv none [])] })
    (safe : result ≠ .err (.abort .typeError))
    (generation : envGenRel ⟨0, config.envs.next, .ln⟩ source.evalState)
    (future : envGenFutureRel interp outGen source.evalState) :
    ∃ finalFlat nextGenv flatError,
      FlatSem.evaluateDecs flat (compileProg config decs).2 = (finalFlat, flatError) ∧
      StateRel nextGenv sourceLast finalFlat ∧
      (∀ resultEnv, result = .val resultEnv → flatError = none ∧ EnvDomainEq outEnv resultEnv ∧
        envGenRel outGen sourceLast.evalState ∧ GlobalEnvInv nextGenv outEnv (fun _ => False) resultEnv) ∧
      (∀ error, result = .err error → ∃ flatErr, flatError = some flatErr ∧
        ResultRel (fun _ (_ : SemEnv Value) (_ : Unit) => True) nextGenv (.err error) (.err flatErr)) := by
  obtain ⟨finalFlat, nextGenv, flatError, flatRun, states, _, success, errors⟩ :=
    factoredCompileDeclarations interp transform decs genv config.modEnv outEnv sourceEnv [] source sourceLast
      { flat with globals := some (.loc true 0) :: List.replicate (next.vidx - config.next.vidx - 1) none,
                  refs := [.refv (.conv none [])] }
      { config.next with vidx := config.next.vidx + 1 } next next ∅ 1 n ⟨0, config.envs.next, .ln⟩ outGen body result
      sourceRun invariant compiled (initGlobalEnvInv_imp genv config.modEnv sourceEnv initialEnv)
      safe generation future (idxPrev_refl next)
  refine ⟨finalFlat, nextGenv, flatError, ?_, states, success, errors⟩
  rw [evaluateCompileProg_continue flat config decs n next outEnv outGen body globalsEmpty refsEmpty compiled]
  exact flatRun

/-- Whole-program simulation under the original initialization conditions,
using preliminary factored relations whose HOL correspondence remains under
review. -/
theorem factoredCompileProg_initial {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (config : Config) (decs : List Dec) (sourceEnv : SemEnv Value)
    (source sourceLast : State F) (flat : FlatSem.State C F)
    (n : Nat) (next : NextIndices) (outEnv : Environment) (outGen : EnvironmentGenerationStore)
    (body : List FlatLang.Exp) (result : Result (SemEnv Value) Value)
    (compiled : compileDecs [] 1 { config.next with vidx := config.next.vidx + 1 } config.modEnv
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, outEnv, outGen, body))
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv decs = (sourceLast, result))
    (globalsEmpty : flat.globals = []) (refsEmpty : flat.refs = [])
    (initialEnv : InitialEnv.initGlobalEnvInv initGenv config.modEnv sourceEnv)
    (safe : result ≠ .err (.abort .typeError))
    (startVar : config.next.vidx = 0) (initialIdx : idxPrev initGenvNext config.next)
    (emptyStore : config.envs = emptyConfig.envs) (initialEval : initEvalStateOk source.evalState)
    (steps : srcOracStepInvs interp transform source.evalState)
    (oracle : oracRel interp transform source.evalState flat.evalConfig)
    (stamps : ∀ entry ∈ initGenvEntries, match entry.2 with
      | .typeStamp _ index => index < source.nextTypeStamp
      | .exnStamp index => index < source.nextExnStamp)
    (sourceRefs : source.refs = []) (clock : source.clock = flat.clock) (ffi : source.ffi = flat.ffi)
    (oracleConfig : match srcOracNextCfg interp source.evalState with
      | none => True
      | some nextConfig => nextConfig = (compileProg config decs).1) :
    ∃ finalFlat nextGenv flatError,
      FlatSem.evaluateDecs flat (compileProg config decs).2 = (finalFlat, flatError) ∧
      StateRel nextGenv sourceLast finalFlat ∧
      (∀ resultEnv, result = .val resultEnv → flatError = none ∧ EnvDomainEq outEnv resultEnv ∧
        envGenRel outGen sourceLast.evalState ∧ GlobalEnvInv nextGenv outEnv (fun _ => False) resultEnv) ∧
      (∀ error, result = .err error → ∃ flatErr, flatError = some flatErr ∧
        ResultRel (fun _ (_ : SemEnv Value) (_ : Unit) => True) nextGenv (.err error) (.err flatErr)) := by
  apply factoredCompileProg_prepared interp transform config decs
    { initGenv with v := some (.loc true 0) ::
        List.replicate (next.vidx - config.next.vidx - 1) none } sourceEnv source sourceLast flat
    n next outEnv outGen body result compiled sourceRun globalsEmpty refsEmpty
  · simpa [InitialEnv.initGlobalEnvInv] using initialEnv
  · exact factoredInvariant_compileProg_initial interp transform config decs source flat n next outEnv outGen body
      compiled startVar initialIdx emptyStore initialEval steps oracle oracleConfig stamps sourceRefs clock ffi
  · exact safe
  · simpa [emptyStore, emptyConfig] using initEvalStateOk_envGenRel source.evalState initialEval
  · exact compileProg_envGenFutureRel interp source.evalState config decs n next outEnv outGen body compiled oracleConfig

/-- The source whole-program precondition, preserving independent compiler,
FFI, and initial-environment value types. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "precondition1_def"]
noncomputable def FactoredPrecondition1 {C F A : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv A) (config : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) : Prop :=
  srcOracStepInvs interp transform source.evalState ∧
  oracRel interp transform source.evalState evalConfig ∧
  (match srcOracNextCfg interp source.evalState with
    | none => True | some nextConfig => nextConfig = (compileProg config decs).1) ∧
  config.next.vidx = 0 ∧ source.refs = [] ∧
  InitialEnv.initGlobalEnvInv initGenv config.modEnv sourceEnv ∧
  initEvalStateOk source.evalState ∧ idxPrev initGenvNext config.next ∧
  (∀ entry ∈ initGenvEntries, match entry.2 with
    | .typeStamp _ index => index < source.nextTypeStamp
    | .exnStamp index => index < source.nextExnStamp) ∧
  config.envs = emptyConfig.envs

/-- Changing the source clock preserves the whole-program precondition. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "precondition1_change_clock"]
theorem factoredPrecondition1_changeClock {C F A : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv A) (config : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) (clock : Nat)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs) :
    FactoredPrecondition1 interp transform { source with clock } sourceEnv config evalConfig decs := by
  simpa [FactoredPrecondition1] using precondition

/-- Whole-program simulation with the source and target results related. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_prog_correct"
  (fmap_as_finite_support := [c, tys])]
theorem factoredCompileProg_correct {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source sourceLast : State F) (sourceEnv : SemEnv Value) (config outputConfig : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (result : Result (SemEnv Value) Value)
    (premises : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs ∧
      compileProg config decs = (outputConfig, flatDecs) ∧
      EvaluateHOL.evaluateDecs source sourceEnv decs = (sourceLast, result) ∧
      result ≠ .err (.abort .typeError)) :
    ∃ (initialFlat finalFlat : FlatSem.State C F) (nextGenv : GlobalEnv), ∃ flatError,
      initialFlat = FlatSem.initialState source.ffi source.clock evalConfig ∧
      FlatSem.evaluateDecs initialFlat flatDecs = (finalFlat, flatError) ∧
      StateRel nextGenv sourceLast finalFlat ∧
      (∀ resultEnv, result = .val resultEnv → flatError = none) ∧
      (∀ error, result = .err error → ∃ flatErr, flatError = some flatErr ∧
        flatErr ≠ .abort .typeError ∧
        ResultRel (fun _ (_ : Unit) (_ : Unit) => True) nextGenv (.err error) (.err flatErr)) := by
  obtain ⟨precondition, compiled, sourceRun, safe⟩ := premises
  obtain ⟨steps, oracle, oracleConfig, startVar, sourceRefs, initialEnv, initialEval, initialIdx, stamps, emptyStore⟩ :=
    precondition
  generalize bodyCompiled : compileDecs [] 1 { config.next with vidx := config.next.vidx + 1 } config.modEnv
    ⟨0, config.envs.next, .ln⟩ decs = compiledResult
  obtain ⟨n, next, outEnv, outGen, body⟩ := compiledResult
  have actual := factoredCompileProg_initial interp transform config decs sourceEnv source sourceLast
    (FlatSem.initialState source.ffi source.clock evalConfig)
    n next outEnv outGen body result bodyCompiled sourceRun rfl rfl
    initialEnv safe startVar initialIdx emptyStore
    initialEval steps oracle stamps sourceRefs rfl rfl oracleConfig
  obtain ⟨finalFlat, nextGenv, flatError, flatRun, states, success, errors⟩ := actual
  refine ⟨FlatSem.initialState source.ffi source.clock evalConfig, finalFlat, nextGenv, flatError,
    rfl, ?_, states, ?_, ?_⟩
  · simpa [compiled] using flatRun
  · intro resultEnv resultEq
    exact (success resultEnv resultEq).1
  · intro error resultEq
    obtain ⟨flatErr, flatEq, related⟩ := errors error resultEq
    refine ⟨flatErr, flatEq, ?_, ?_⟩
    · intro flatTypeError
      subst flatErr
      cases related
      exact safe resultEq
    · cases related with
      | raise related => exact .raise related
      | abort error => exact .abort error

/-- Source type safety at every clock rules out a flat type error at every
clock for the compiled program, over the factored simulation relations. -/
theorem factoredCompileProg_noTypeError {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config outputConfig : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs)
    (compiled : compileProg config decs = (outputConfig, flatDecs))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail) :
    ∀ clock, (FlatSem.evaluateDecs (FlatSem.initialState source.ffi clock evalConfig) flatDecs).2 ≠
      some (.abort .typeError) := by
  intro clock
  generalize sourceRun : EvaluateHOL.evaluateDecs { source with clock } sourceEnv decs = resultPair
  obtain ⟨sourceLast, result⟩ := resultPair
  have sourceSafe : result ≠ .err (.abort .typeError) := by
    intro error
    apply safe
    change ∃ k, (Flapjack.SemanticsHOL.evaluateProgWithClock source sourceEnv k decs).2 =
      .err (.abort .typeError)
    refine ⟨clock, ?_⟩
    simp [Flapjack.SemanticsHOL.evaluateProgWithClock, sourceRun, error]
  obtain ⟨initialFlat, flatLast, genv, flatError, initialEq, flatRun, _, success, errors⟩ :=
    factoredCompileProg_correct interp transform { source with clock } sourceLast sourceEnv config outputConfig
      evalConfig decs flatDecs result
      ⟨factoredPrecondition1_changeClock interp transform source sourceEnv config evalConfig decs clock precondition,
        compiled, sourceRun, sourceSafe⟩
  subst initialFlat
  rw [flatRun]
  cases result with
  | val env => simp [success env rfl]
  | err error =>
    obtain ⟨flatErr, eq, notTypeError, _⟩ := errors error rfl
    simp [eq, notTypeError]

/-- The compiled flat program cannot have failure behavior when the source
program is safe, under the factored source-to-flat preconditions. -/
theorem factoredCompileProg_semantics_ne_fail {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config outputConfig : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs)
    (compiled : compileProg config decs = (outputConfig, flatDecs))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail) :
    FlatSem.semantics evalConfig source.ffi flatDecs ≠ .fail := by
  exact FlatSem.semantics_ne_fail evalConfig source.ffi flatDecs
    (factoredCompileProg_noTypeError interp transform source sourceEnv config outputConfig
      evalConfig decs flatDecs precondition compiled safe)

/-- Every terminating flat observation is a source-program observation,
including the outcome and complete FFI event list. This uses the preliminary
factored simulation relations. -/
theorem factoredCompileProg_semantics_terminate {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config outputConfig : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs)
    (compiled : compileProg config decs = (outputConfig, flatDecs))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : FlatSem.semantics evalConfig source.ffi flatDecs = .terminate outcome events) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs (.terminate outcome events) := by
  obtain ⟨clock, flatLast, flatResult, flatRun, flatOutcome, eventEq⟩ :=
    FlatSem.semantics_terminate evalConfig source.ffi flatDecs outcome events terminates
  generalize sourceRun : EvaluateHOL.evaluateDecs { source with clock } sourceEnv decs = sourcePair
  obtain ⟨sourceLast, result⟩ := sourcePair
  have sourceSafe : result ≠ .err (.abort .typeError) := by
    intro error
    apply safe
    change ∃ k, (Flapjack.SemanticsHOL.evaluateProgWithClock source sourceEnv k decs).2 =
      .err (.abort .typeError)
    refine ⟨clock, ?_⟩
    simp [Flapjack.SemanticsHOL.evaluateProgWithClock, sourceRun, error]
  obtain ⟨initialFlat, actualFlat, genv, actualResult, initialEq, actualRun, states, success, errors⟩ :=
    factoredCompileProg_correct interp transform { source with clock } sourceLast sourceEnv config outputConfig
      evalConfig decs flatDecs result
      ⟨factoredPrecondition1_changeClock interp transform source sourceEnv config evalConfig decs clock precondition,
        compiled, sourceRun, sourceSafe⟩
  subst initialFlat
  rw [flatRun] at actualRun
  cases actualRun
  have equalFfi : sourceLast.ffi = flatLast.ffi := (stateRel_iff _ _ _).mp states |>.2.2.2
  refine ⟨clock, sourceLast.ffi, result, ?_, ?_, ?_, sourceSafe⟩
  · simp [Flapjack.SemanticsHOL.evaluateProgWithClock, sourceRun]
  · cases result with
    | val env =>
      have eq := success env rfl
      subst flatResult
      simpa using flatOutcome
    | err error =>
      obtain ⟨flatError, eq, _, related⟩ := errors error rfl
      subst flatResult
      cases related with
      | raise related => simpa using flatOutcome
      | abort error =>
        cases error with
        | typeError => exact False.elim (sourceSafe rfl)
        | timeoutError => exact False.elim flatOutcome
        | ffiError event => simpa using flatOutcome
  · simpa [equalFfi] using eventEq

/-- Divergence of the flat program forces the source run to time out at
every clock, under the factored compilation conditions. -/
theorem factoredCompileProg_diverge_sourceTimeout {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config outputConfig : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs)
    (compiled : compileProg config decs = (outputConfig, flatDecs))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail)
    (events : HolLList HolIoEvent)
    (diverges : FlatSem.semantics evalConfig source.ffi flatDecs = .diverge events) :
    ∀ clock, ∃ ffi, Flapjack.SemanticsHOL.evaluateProgWithClock source sourceEnv clock decs =
      (ffi, .err (.abort .timeoutError)) := by
  have noTerm := (FlatSem.semantics_diverge evalConfig source.ffi flatDecs events diverges).1
  intro clock
  generalize sourceRun : EvaluateHOL.evaluateDecs { source with clock } sourceEnv decs = sourcePair
  obtain ⟨sourceLast, result⟩ := sourcePair
  have sourceSafe : result ≠ .err (.abort .typeError) := by
    intro error
    apply safe
    change ∃ k, (Flapjack.SemanticsHOL.evaluateProgWithClock source sourceEnv k decs).2 =
      .err (.abort .typeError)
    refine ⟨clock, ?_⟩
    simp [Flapjack.SemanticsHOL.evaluateProgWithClock, sourceRun, error]
  obtain ⟨initialFlat, flatLast, genv, flatResult, initialEq, flatRun, _, success, errors⟩ :=
    factoredCompileProg_correct interp transform { source with clock } sourceLast sourceEnv config outputConfig
      evalConfig decs flatDecs result
      ⟨factoredPrecondition1_changeClock interp transform source sourceEnv config evalConfig decs clock precondition,
        compiled, sourceRun, sourceSafe⟩
  subst initialFlat
  have timeout : result = .err (.abort .timeoutError) := by
    cases result with
    | val env =>
      have eq := success env rfl
      subst flatResult
      exact False.elim (noTerm clock flatLast none .success flatRun rfl)
    | err error =>
      obtain ⟨flatError, eq, _, related⟩ := errors error rfl
      subst flatResult
      cases related with
      | raise related =>
        exact False.elim (noTerm clock flatLast (some (.raise _)) .success flatRun rfl)
      | abort error =>
        cases error with
        | typeError => exact False.elim (sourceSafe rfl)
        | timeoutError => rfl
        | ffiError event =>
          exact False.elim (noTerm clock flatLast (some (.abort (.ffiError event))) (.ffiOutcome event) flatRun rfl)
  exact ⟨sourceLast.ffi, by simp [Flapjack.SemanticsHOL.evaluateProgWithClock, sourceRun, timeout]⟩

/-- Every clock produces the same FFI state in the source and flat runs. -/
theorem factoredCompileProg_clockFfi {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config outputConfig : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs)
    (compiled : compileProg config decs = (outputConfig, flatDecs))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail)
    (clock : Nat) :
    (Flapjack.SemanticsHOL.evaluateProgWithClock source sourceEnv clock decs).1 =
      (FlatSem.evaluateDecs (FlatSem.initialState source.ffi clock evalConfig) flatDecs).1.ffi := by
  generalize sourceRun : EvaluateHOL.evaluateDecs { source with clock } sourceEnv decs = sourcePair
  obtain ⟨sourceLast, result⟩ := sourcePair
  have sourceSafe : result ≠ .err (.abort .typeError) := by
    intro error
    apply safe
    change ∃ k, (Flapjack.SemanticsHOL.evaluateProgWithClock source sourceEnv k decs).2 =
      .err (.abort .typeError)
    refine ⟨clock, ?_⟩
    simp [Flapjack.SemanticsHOL.evaluateProgWithClock, sourceRun, error]
  obtain ⟨initialFlat, flatLast, genv, flatResult, initialEq, flatRun, states, _, _⟩ :=
    factoredCompileProg_correct interp transform { source with clock } sourceLast sourceEnv config outputConfig
      evalConfig decs flatDecs result
      ⟨factoredPrecondition1_changeClock interp transform source sourceEnv config evalConfig decs clock precondition,
        compiled, sourceRun, sourceSafe⟩
  subst initialFlat
  have ffiEq := (stateRel_iff genv sourceLast flatLast).mp states |>.2.2.2
  simpa [Flapjack.SemanticsHOL.evaluateProgWithClock, sourceRun, flatRun] using ffiEq

/-- A flat divergence observation is a source divergence observation,
including equality of the complete least-upper-bound event trace. -/
theorem factoredCompileProg_semantics_diverge {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config outputConfig : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs)
    (compiled : compileProg config decs = (outputConfig, flatDecs))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail)
    (events : HolLList HolIoEvent)
    (diverges : FlatSem.semantics evalConfig source.ffi flatDecs = .diverge events) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs (.diverge events) := by
  refine ⟨factoredCompileProg_diverge_sourceTimeout interp transform source sourceEnv config outputConfig
    evalConfig decs flatDecs precondition compiled safe events diverges, ?_⟩
  have eventEq := (FlatSem.semantics_diverge evalConfig source.ffi flatDecs events diverges).2
  have families : (fun trace => ∃ clock,
      trace = HolLList.fromList (FlatSem.evaluateDecs (FlatSem.initialState source.ffi clock evalConfig) flatDecs).1.ffi.ioEvents) =
      (fun trace => ∃ clock,
        HolLList.fromList (Flapjack.SemanticsHOL.evaluateProgWithClock source sourceEnv clock decs).1.ioEvents = trace) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, eq⟩ <;> refine ⟨clock, ?_⟩
    · rw [factoredCompileProg_clockFfi interp transform source sourceEnv config outputConfig
        evalConfig decs flatDecs precondition compiled safe clock]
      exact eq.symm
    · rw [factoredCompileProg_clockFfi interp transform source sourceEnv config outputConfig
        evalConfig decs flatDecs precondition compiled safe clock] at eq
      exact eq.symm
  rw [families] at eventEq
  rw [eventEq]
  exact HolLList.buildLprefixLub_thm (Flapjack.SemanticsProps.evaluateProg_ioEventsChain source sourceEnv decs)

/-- A pair has a given second component exactly when it can be decomposed with it. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "SND_eq"]
theorem snd_eq_iff {α β : Type} (x : α × β) (y : β) :
    x.2 = y ↔ ∃ a, x = (a, y) := by
  cases x with
  | mk a b => simp

/-- The compiled flat program's observable behavior is a source behavior. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_prog_semantics"]
theorem factoredCompileProg_semantics {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs)
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs
      (FlatSem.semantics evalConfig source.ffi (compileProg config decs).2) := by
  cases compiled : compileProg config decs with
  | mk outputConfig flatDecs =>
   cases behavior : FlatSem.semantics evalConfig source.ffi flatDecs with
   | fail =>
     exact False.elim (factoredCompileProg_semantics_ne_fail interp transform source sourceEnv config outputConfig
       evalConfig decs flatDecs precondition compiled safe behavior)
   | terminate outcome events =>
     exact factoredCompileProg_semantics_terminate interp transform source sourceEnv config outputConfig
       evalConfig decs flatDecs precondition compiled safe outcome events behavior
   | diverge events =>
     exact factoredCompileProg_semantics_diverge interp transform source sourceEnv config outputConfig
       evalConfig decs flatDecs precondition compiled safe events behavior

end Flapjack.Compiler.Backend.SourceToFlat
