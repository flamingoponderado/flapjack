import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateModule
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateException
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDatatype
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLiteralConstructors
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingConstructors
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingRaise
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingLet
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingIf
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingLog
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingArith
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalArray
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedArrayTree

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
  | literalConstructor (location : Flapjack.Misc.Location.Locs) (pattern : Pat)
      (name : Option (Ident ModN ConN)) (lits : List Lit) :
      FactoredScopedDec (.dlet location pattern (.con name (lits.map AstHOL.Exp.lit)))
  | pureConstructor (location : Flapjack.Misc.Location.Locs) (pattern : Pat)
      (name : Option (Ident ModN ConN)) (args : List (Lit ⊕ (VarN × AstHOL.Exp))) :
      FactoredScopedDec (.dlet location pattern (.con name (args.map pureConstructorArgument)))
  | constructorExpression (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      FactoredConstructorExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | raisedExpression (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      FactoredRaisedExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | letExpression (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      FactoredLetExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | ifExpression (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      FactoredIfExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | logExpression (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      FactoredLogExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | arithExpression (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      FactoredArithExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | testExpression (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      FactoredTestExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | equalityExpression (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      FactoredEqualityExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | namedSelf (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (name : VarN) (first : AstHOL.Exp) :
      FactoredEqualityExpression first →
      FactoredScopedDec (.dlet location pattern (.let_ (some name) first (.var (.short name))))
  | boundExpression (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      FactoredBoundExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | boundLocal (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (name : VarN) (first body : AstHOL.Exp) :
      FactoredBoundExpression first → BoundLocalExpression name body →
      FactoredScopedDec (.dlet location pattern (.let_ (some name) first body))
  | boundRecursive (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (name : VarN) (first body : AstHOL.Exp) :
      FactoredBoundExpression first → BoundRecursiveExpression name body →
      FactoredScopedDec (.dlet location pattern (.let_ (some name) first body))
  | boundTuple (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (name : VarN) (first body : AstHOL.Exp) :
      FactoredBoundExpression first → BoundTupleExpression name body →
      FactoredScopedDec (.dlet location pattern (.let_ (some name) first body))
  | boundConstructor (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (name : VarN) (first body : AstHOL.Exp) :
      FactoredBoundExpression first → BoundConstructorExpression name body →
      FactoredScopedDec (.dlet location pattern (.let_ (some name) first body))
  | boundControl (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (name : VarN) (first body : AstHOL.Exp) :
      FactoredBoundExpression first → BoundControlExpression name body →
      FactoredScopedDec (.dlet location pattern (.let_ (some name) first body))
  | localEnvironment (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      LocalEnvExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | localControl (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      LocalEnvControlExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | localConstructor (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      LocalEnvConstructorExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | localPrimitive (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      LocalEnvPrimitiveExpression expr → FactoredScopedDec (.dlet location pattern expr)
  | localArray (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      LocalEnvArrayExpression expr → FactoredScopedDec (.dlet location pattern expr)
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
  | literalConstructor location pattern name lits =>
    exact factoredDecIH_dlet_literalConstructor interp transform location pattern name lits
  | pureConstructor location pattern name args =>
    exact factoredDecIH_dlet_pureConstructor interp transform location pattern name args
  | constructorExpression location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (factoredExpressionIH_constructorTree interp transform expr covered)
  | raisedExpression location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (factoredExpressionIH_raisedTree interp transform expr covered)
  | letExpression location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (factoredExpressionIH_letTree interp transform expr covered)
  | ifExpression location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (factoredExpressionIH_ifTree interp transform expr covered)
  | logExpression location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (factoredExpressionIH_logTree interp transform expr covered)
  | arithExpression location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (factoredExpressionIH_arithTree interp transform expr covered)
  | testExpression location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (factoredExpressionIH_testTree interp transform expr covered)
  | equalityExpression location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (factoredExpressionIH_equalityTree interp transform expr covered)
  | namedSelf location pattern name first covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern _
      (factoredExpressionIH_let_named_self interp transform name first
        (factoredExpressionIH_equalityTree interp transform first covered))
  | boundExpression location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (factoredExpressionIH_boundTree interp transform expr covered)
  | boundLocal location pattern name first body firstCovered bodyCovered =>
    exact factoredDecIH_dlet_expression interp transform location pattern _
      (factoredExpressionIH_let_named_local interp transform name first body bodyCovered
        (factoredExpressionIH_boundTree interp transform first firstCovered))
  | boundRecursive location pattern name first body firstCovered bodyCovered =>
    exact factoredDecIH_dlet_expression interp transform location pattern _
      (factoredExpressionIH_let_named_recursive interp transform name first body bodyCovered
        (factoredExpressionIH_boundTree interp transform first firstCovered))
  | boundTuple location pattern name first body firstCovered bodyCovered =>
    exact factoredDecIH_dlet_expression interp transform location pattern _
      (factoredExpressionIH_let_named_tuple interp transform name first body bodyCovered
        (factoredExpressionIH_boundTree interp transform first firstCovered))
  | boundConstructor location pattern name first body firstCovered bodyCovered =>
    exact factoredDecIH_dlet_expression interp transform location pattern _
      (factoredExpressionIH_let_named_constructor interp transform name first body bodyCovered
        (factoredExpressionIH_boundTree interp transform first firstCovered))
  | boundControl location pattern name first body firstCovered bodyCovered =>
    exact factoredDecIH_dlet_expression interp transform location pattern _
      (factoredExpressionIH_let_named_control interp transform name first body bodyCovered
        (factoredExpressionIH_boundTree interp transform first firstCovered))
  | localEnvironment location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (localEnvIH_to_factored interp transform expr (localEnvIH_covered interp transform expr covered))
  | localControl location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (localEnvIH_to_factored interp transform expr (localEnvIH_controlTree interp transform expr covered))
  | localConstructor location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (localEnvIH_to_factored interp transform expr (localEnvIH_constructorTree interp transform expr covered))
  | localPrimitive location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (localEnvIH_to_factored interp transform expr (localEnvIH_primitiveTree interp transform expr covered))
  | localArray location pattern expr covered =>
    exact factoredDecIH_dlet_expression interp transform location pattern expr
      (localEnvIH_to_factored interp transform expr (localEnvIH_arrayTree interp transform expr covered))
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

/-- Declaration forms with bounded simulations, including value declarations
whose initializers use the bounded expression proof. -/
inductive FactoredBoundedDec : Dec → Prop where
  | existing (dec : Dec) : FactoredScopedDec dec → FactoredBoundedDec dec
  | value (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression expr → FactoredBoundedDec (.dlet location pattern expr)
  | module_ (moduleName : ModN) (decs : List Dec) :
      (∀ dec, dec ∈ decs → FactoredBoundedDec dec) → FactoredBoundedDec (.dmod moduleName decs)
  | local_ (locals body : List Dec) :
      (∀ dec, dec ∈ locals → FactoredBoundedDec dec) →
      (∀ dec, dec ∈ body → FactoredBoundedDec dec) → FactoredBoundedDec (.dlocal locals body)

/-- Every source declaration has a structural bounded-coverage derivation. -/
theorem allDeclarations_covered : (dec : Dec) → FactoredBoundedDec dec
  | .dlet location pattern expr => .value location pattern expr (allExpressions_covered expr)
  | .dletrec location funs => .existing _ (.basic _ (.letrec location funs))
  | .dtype location types => .existing _ (.datatype_ location types)
  | .dtabbrev location vars name typ => .existing _ (.basic _ (.tabbrev location vars name typ))
  | .dexn location name types => .existing _ (.exception_ location name types)
  | .dmod name decs => .module_ name decs (fun dec _member => allDeclarations_covered dec)
  | .dlocal locals body => .local_ locals body
      (fun dec _member => allDeclarations_covered dec) (fun dec _member => allDeclarations_covered dec)
  | .denv name => .existing _ (.basic _ (.denv name))
termination_by dec => sizeOf dec
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem _member
  all_goals omega

/-- Singleton simulations for recursively covered bounded declarations. -/
theorem factoredDecBoundedIH_covered {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (smallerExprs : ∀ n, n < limit → ∀ expr, LocalEnvBoundedIH (F := F) interp transform n expr)
    (smallerDecs : ∀ n, n < limit → ∀ decs, FactoredDecBoundedIH (F := F) interp transform n decs)
    (dec : Dec) (covered : FactoredBoundedDec dec) :
    FactoredDecBoundedIH (F := F) interp transform limit [dec] := by
  induction covered with
  | existing dec covered =>
    exact factoredDecBoundedIH_of_unbounded interp transform limit [dec] (factoredDecIH_scoped interp transform dec covered)
  | value location pattern expr covered =>
    exact factoredDecBoundedIH_dlet_arrayTree interp transform limit smallerExprs smallerDecs location pattern expr covered
  | module_ moduleName decs _ ih =>
    apply factoredDecBoundedIH_dmod interp transform limit moduleName decs
    apply factoredDecBoundedIH_list interp transform limit decs
    exact ih
  | local_ locals body _ _ localIH bodyIH =>
    apply factoredDecBoundedIH_dlocal interp transform limit locals body
    · apply factoredDecBoundedIH_list interp transform limit locals
      exact localIH
    · apply factoredDecBoundedIH_list interp transform limit body
      exact bodyIH

/-- Covered declaration lists compose under smaller-clock hypotheses. -/
theorem factoredDecBoundedIH_covered_list {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (smallerExprs : ∀ n, n < limit → ∀ expr, LocalEnvBoundedIH (F := F) interp transform n expr)
    (smallerDecs : ∀ n, n < limit → ∀ decs, FactoredDecBoundedIH (F := F) interp transform n decs)
    (decs : List Dec) (covered : ∀ dec, dec ∈ decs → FactoredBoundedDec dec) :
    FactoredDecBoundedIH (F := F) interp transform limit decs := by
  apply factoredDecBoundedIH_list interp transform limit decs
  intro dec member
  exact factoredDecBoundedIH_covered interp transform limit smallerExprs smallerDecs dec (covered dec member)

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
        (allExpressions_covered expr)
    · intro decs
      exact factoredDecBoundedIH_covered_list interp transform limit smallerExprs smallerDecs decs
        (fun dec _ => allDeclarations_covered dec)

/-- Arbitrary source expressions satisfy the preliminary local simulation.
The factored relations are not yet reviewed as the original HOL theorem. -/
theorem localEnvIH_all {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) : LocalEnvIH (F := F) interp transform expr := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
  exact (factoredAllBounded (F := F) interp transform source.clock).1 expr genv start finish other
    source flat baseEnv sourceLocal flatEnv traces trace baseMap gen (Nat.le_refl _)

/-- Arbitrary source declaration lists satisfy the preliminary factored
simulation. This is not yet the reviewed HOL pass-correctness statement. -/
theorem factoredDecIH_all {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (decs : List Dec) : FactoredDecIH (F := F) interp transform decs := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen flatDecs result
  exact (factoredAllBounded (F := F) interp transform source.clock).2 decs genv env nextEnv sourceEnv trace
    source sourceLast flat start finish next other n n' gen nextGen flatDecs result (Nat.le_refl _)

end Flapjack.Compiler.Backend.SourceToFlat
