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
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.Initialization
import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics
import Flapjack.SemanticsHOL

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

/-- The original initialization condition expressed using the preliminary
factored global relation. Full cross-language correspondence remains under review. -/
def FactoredInitGlobalEnvInv (genv : GlobalEnv) (compMap : Environment) (env : SemEnv Value) : Prop :=
  env.v = nsEmpty ∧
    match env.c with
    | .bind entries modules => modules = [] ∧ ∀ name arity stamp, (name, (arity, stamp)) ∈ entries →
        ∃ cn tyGroup, nsLookup compMap.c (.short name) = some (cn, tyGroup) ∧
          genv.c.lookup ((cn, tyGroup.map Prod.fst), arity) = some stamp ∧
          ∀ tyId ctors, tyGroup = some (tyId, ctors) → genv.tys.lookup tyId = some ctors

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

/-- The factored initialization condition supplies the global environment
invariant needed by declaration simulation. -/
theorem factoredInitGlobalEnvInv_imp (genv : GlobalEnv) (compMap : Environment) (env : SemEnv Value)
    (initial : FactoredInitGlobalEnvInv genv compMap env) :
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
        exact entriesValid name arity stamp member

/-- HOL-shaped combined environment relation using the preliminary factored
value and global relations. Its full HOL correspondence remains under review. -/
def FactoredEnvAllRel (genv : GlobalEnv) (compMap : Environment) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN) : Prop :=
  ∃ (baseEnv : SemEnv Value) (sourceLocal : Namespace ModN VarN Value) (bindings : List (VarN × Value)),
    sourceEnv = { baseEnv with v := nsAppend sourceLocal baseEnv.v } ∧
    sourceLocal = alistToNs bindings ∧ bindings.map Prod.fst = locals ∧
    GlobalEnvInv genv compMap (fun name => name ∈ locals) baseEnv ∧ EnvRel genv sourceLocal flatEnv.v

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

/-- Arbitrary source expression lists satisfy the preliminary factored
simulation. HOL correspondence of its relations remains under review. -/
theorem factoredExpressionList_all {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (exprs : List AstHOL.Exp) (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (sourceLocal : Namespace ModN VarN Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (traces : List BackendCommon.Tra) (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
    (localRel : EnvRel genv sourceLocal flatEnv.v)
    (envInv : GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv)
    (tracesLen : traces.length = flatEnv.v.length)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsAppend sourceLocal baseEnv.v } exprs ≠
      (last, .err (.abort .typeError))) :
    LocalExpressionListStep interp transform genv start finish other source flat
      { baseEnv with v := nsAppend sourceLocal baseEnv.v } flatEnv trace
      { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } gen exprs := by
  exact boundedEnvListStep_of_each interp transform source.clock exprs
    (fun expr _ => (factoredAllBounded (F := F) interp transform source.clock).1 expr)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    (Nat.le_refl _) localRel envInv tracesLen invariant generation safe

/-- Expression-list simulation exposed through the combined environment
relation used in the original theorem's statement. -/
theorem factoredExpressionList_envAll {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (exprs : List AstHOL.Exp) (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN)
    (traces : List BackendCommon.Tra) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (envRel : FactoredEnvAllRel genv compMap sourceEnv flatEnv locals)
    (tracesLen : traces.length = locals.length)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source sourceEnv exprs ≠ (last, .err (.abort .typeError))) :
    LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace
      { compMap with v := bindLocals traces locals compMap.v } gen exprs := by
  have names := factoredEnvAllRel_names genv compMap sourceEnv flatEnv locals envRel
  subst locals
  obtain ⟨baseEnv, sourceLocal, bindings, sourceEq, _, _, envInv, localRel⟩ := envRel
  subst sourceEnv
  exact factoredExpressionList_all interp transform exprs genv start finish other source flat baseEnv sourceLocal
    flatEnv traces trace compMap gen localRel envInv (by simpa using tracesLen) invariant generation safe

/-- Expression-list result in the existential shape of the source-to-flat
theorem, over the factored relations. HOL correspondence remains under review. -/
theorem factoredCompileExpressions {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (exprs : List AstHOL.Exp) (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source sourceLast : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN)
    (traces : List BackendCommon.Tra) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (result : Result (List Value) Value)
    (sourceRun : EvaluateHOL.evaluate source sourceEnv exprs = (sourceLast, result))
    (envRel : FactoredEnvAllRel genv compMap sourceEnv flatEnv locals)
    (tracesLen : traces.length = locals.length)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState) (safe : result ≠ .err (.abort .typeError)) :
    ∃ finalFlat flatResult nextGenv,
      FlatSem.evaluate flatEnv flat (compileExps trace { compMap with v := bindLocals traces locals compMap.v } exprs) =
        (finalFlat, flatResult) ∧
      EvalResultRel nextGenv result flatResult ∧ StateRel nextGenv sourceLast finalFlat ∧
      (match result with
       | .err (.abort _) => True
       | _ => GlobalGrowth genv nextGenv ∧
           factoredInvariant interp transform gen nextGenv (start, finish, other) sourceLast finalFlat ∧
           envGenRel gen sourceLast.evalState ∧ oracForwardRel interp source.evalState sourceLast.evalState) := by
  have sourceSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv exprs ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    rw [sourceRun] at bad
    exact safe (Prod.mk.inj bad).2
  obtain ⟨nextGenv, simulation, post⟩ := factoredExpressionList_envAll interp transform exprs genv start finish other
    source flat sourceEnv flatEnv locals traces trace compMap gen envRel tracesLen invariant generation sourceSafe
  unfold ExprListSim at simulation
  generalize flatRun : FlatSem.evaluate flatEnv flat
    (compileExps trace { compMap with v := bindLocals traces locals compMap.v } exprs) = flatPair at simulation post
  obtain ⟨finalFlat, flatResult⟩ := flatPair
  change EvalResultRel nextGenv (EvaluateHOL.evaluate source sourceEnv exprs).2 flatResult ∧
    StateRel nextGenv (EvaluateHOL.evaluate source sourceEnv exprs).1 finalFlat at simulation
  simp only [sourceRun] at simulation
  refine ⟨finalFlat, flatResult, nextGenv, rfl, simulation.1, simulation.2, ?_⟩
  cases result with
  | val values => simpa only [sourceRun] using post
  | err error =>
    cases error with
    | abort _ => trivial
    | raise _ => simpa only [sourceRun] using post

/-- Arbitrary source match rows satisfy the preliminary simulation under the
compiled-row safety condition; HOL correspondence remains under review. -/
theorem factoredEvaluateMatch_all {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (sourceLocal : Namespace ModN VarN Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (traces : List BackendCommon.Tra) (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
    (localRel : EnvRel genv sourceLocal flatEnv.v)
    (envInv : GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv)
    (tracesLen : traces.length = flatEnv.v.length)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (value errorValue : Value) (flatValue flatError : FlatSem.Value)
    (valueRel : ValueRel genv value flatValue) (errorRel : ValueRel genv errorValue flatError)
    (rows : List (Pat × AstHOL.Exp))
    (flatSafe : FlatSem.pmatchRows
      (compilePes trace { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } rows)
      flat flatValue ≠ .typeError)
    (safe : ∀ last, EvaluateHOL.evaluateMatch source { baseEnv with v := nsAppend sourceLocal baseEnv.v }
      value rows errorValue ≠ (last, .err (.abort .typeError)))
    :
    let sourceResult := EvaluateHOL.evaluateMatch source { baseEnv with v := nsAppend sourceLocal baseEnv.v } value rows errorValue
    let flatResult := flatEvaluateMatch flatEnv flat flatValue flatError
      (compilePes trace { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } rows)
    ∃ nextGenv, (EvalResultRel nextGenv sourceResult.2 flatResult.2 ∧ StateRel nextGenv sourceResult.1 flatResult.1) ∧
      match sourceResult.2 with
      | .err (.abort _) => True
      | _ => GlobalGrowth genv nextGenv ∧
          factoredInvariant interp transform gen nextGenv (start, finish, other) sourceResult.1 flatResult.1 ∧
          envGenRel gen sourceResult.1.evalState ∧ oracForwardRel interp source.evalState sourceResult.1.evalState := by
  exact boundedEvaluateMatch_related_flatSafe interp transform source.clock genv start finish other
    source flat baseEnv sourceLocal flatEnv traces trace baseMap gen (Nat.le_refl _) localRel envInv tracesLen
    invariant generation value errorValue flatValue flatError valueRel errorRel rows flatSafe safe
    (fun _ body _ => (factoredAllBounded (F := F) interp transform source.clock).1 body)


/-- Match-row simulation exposed through the combined environment relation.
The factored carriers still require HOL correspondence review. -/
theorem factoredEvaluateMatch_envAll {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN)
    (traces : List BackendCommon.Tra) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (envRel : FactoredEnvAllRel genv compMap sourceEnv flatEnv locals)
    (tracesLen : traces.length = locals.length)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (value errorValue : Value) (flatValue flatError : FlatSem.Value)
    (valueRel : ValueRel genv value flatValue) (errorRel : ValueRel genv errorValue flatError)
    (rows : List (Pat × AstHOL.Exp))
    (flatSafe : FlatSem.pmatchRows (compilePes trace { compMap with v := bindLocals traces locals compMap.v } rows)
      flat flatValue ≠ .typeError)
    (safe : ∀ last, EvaluateHOL.evaluateMatch source sourceEnv value rows errorValue ≠
      (last, .err (.abort .typeError))) :
    let sourceResult := EvaluateHOL.evaluateMatch source sourceEnv value rows errorValue
    let flatResult := flatEvaluateMatch flatEnv flat flatValue flatError
      (compilePes trace { compMap with v := bindLocals traces locals compMap.v } rows)
    ∃ nextGenv, (EvalResultRel nextGenv sourceResult.2 flatResult.2 ∧ StateRel nextGenv sourceResult.1 flatResult.1) ∧
      match sourceResult.2 with
      | .err (.abort _) => True
      | _ => GlobalGrowth genv nextGenv ∧
          factoredInvariant interp transform gen nextGenv (start, finish, other) sourceResult.1 flatResult.1 ∧
          envGenRel gen sourceResult.1.evalState ∧ oracForwardRel interp source.evalState sourceResult.1.evalState := by
  have names := factoredEnvAllRel_names genv compMap sourceEnv flatEnv locals envRel
  subst locals
  obtain ⟨baseEnv, sourceLocal, bindings, sourceEq, _, _, envInv, localRel⟩ := envRel
  subst sourceEnv
  exact factoredEvaluateMatch_all interp transform genv start finish other source flat baseEnv sourceLocal flatEnv
    traces trace compMap gen localRel envInv (by simpa using tracesLen) invariant generation value errorValue
    flatValue flatError valueRel errorRel rows flatSafe safe

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
    (initialEnv : FactoredInitGlobalEnvInv genv config.modEnv sourceEnv)
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
      sourceRun invariant compiled (factoredInitGlobalEnvInv_imp genv config.modEnv sourceEnv initialEnv)
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
    (initialEnv : FactoredInitGlobalEnvInv initGenv config.modEnv sourceEnv)
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
  · simpa [FactoredInitGlobalEnvInv] using initialEnv
  · exact factoredInvariant_compileProg_initial interp transform config decs source flat n next outEnv outGen body
      compiled startVar initialIdx emptyStore initialEval steps oracle oracleConfig stamps sourceRefs clock ffi
  · exact safe
  · simpa [emptyStore, emptyConfig] using initEvalStateOk_envGenRel source.evalState initialEval
  · exact compileProg_envGenFutureRel interp source.evalState config decs n next outEnv outGen body compiled oracleConfig

/-- Whole-program preconditions over the factored global environment
relation. The relation's cross-language correspondence remains under review. -/
noncomputable def FactoredPrecondition1 {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) : Prop :=
  srcOracStepInvs interp transform source.evalState ∧
  oracRel interp transform source.evalState evalConfig ∧
  (match srcOracNextCfg interp source.evalState with
    | none => True | some nextConfig => nextConfig = (compileProg config decs).1) ∧
  config.next.vidx = 0 ∧ source.refs = [] ∧
  FactoredInitGlobalEnvInv initGenv config.modEnv sourceEnv ∧
  initEvalStateOk source.evalState ∧ idxPrev initGenvNext config.next ∧
  (∀ entry ∈ initGenvEntries, match entry.2 with
    | .typeStamp _ index => index < source.nextTypeStamp
    | .exnStamp index => index < source.nextExnStamp) ∧
  config.envs = emptyConfig.envs

/-- Changing the source clock preserves the factored program precondition. -/
theorem factoredPrecondition1_changeClock {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) (clock : Nat)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs) :
    FactoredPrecondition1 interp transform { source with clock } sourceEnv config evalConfig decs := by
  simpa [FactoredPrecondition1] using precondition

/-- Whole-program simulation in the original existential result shape, over
the preliminary factored relations and precondition. -/
theorem factoredCompileProg_correct {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source sourceLast : State F) (sourceEnv : SemEnv Value) (config outputConfig : Config)
    (evalConfig : FlatSem.InstallConfig C) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (result : Result (SemEnv Value) Value)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config evalConfig decs)
    (compiled : compileProg config decs = (outputConfig, flatDecs))
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv decs = (sourceLast, result))
    (safe : result ≠ .err (.abort .typeError)) :
    ∃ finalFlat nextGenv flatError,
      FlatSem.evaluateDecs (FlatSem.initialState source.ffi source.clock evalConfig) flatDecs = (finalFlat, flatError) ∧
      StateRel nextGenv sourceLast finalFlat ∧
      (∀ resultEnv, result = .val resultEnv → flatError = none) ∧
      (∀ error, result = .err error → ∃ flatErr, flatError = some flatErr ∧
        flatErr ≠ .abort .typeError ∧
        ResultRel (fun _ (_ : SemEnv Value) (_ : Unit) => True) nextGenv (.err error) (.err flatErr)) := by
  obtain ⟨steps, oracle, oracleConfig, startVar, sourceRefs, initialEnv, initialEval, initialIdx, stamps, emptyStore⟩ :=
    precondition
  generalize bodyCompiled : compileDecs [] 1 { config.next with vidx := config.next.vidx + 1 } config.modEnv
    ⟨0, config.envs.next, .ln⟩ decs = compiledResult
  obtain ⟨n, next, outEnv, outGen, body⟩ := compiledResult
  have actual := factoredCompileProg_initial interp transform config decs sourceEnv source sourceLast
    (FlatSem.initialState source.ffi source.clock evalConfig)
    n next outEnv outGen body result bodyCompiled sourceRun rfl rfl initialEnv safe startVar initialIdx emptyStore
    initialEval steps oracle stamps sourceRefs rfl rfl oracleConfig
  obtain ⟨finalFlat, nextGenv, flatError, flatRun, states, success, errors⟩ := actual
  refine ⟨finalFlat, nextGenv, flatError, ?_, states, ?_, ?_⟩
  · simpa [compiled] using flatRun
  · intro resultEnv resultEq
    exact (success resultEnv resultEq).1
  · intro error resultEq
    obtain ⟨flatErr, flatEq, related⟩ := errors error resultEq
    refine ⟨flatErr, flatEq, ?_, related⟩
    intro flatTypeError
    subst flatErr
    cases related
    exact safe resultEq

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
  obtain ⟨flatLast, genv, flatError, flatRun, _, success, errors⟩ :=
    factoredCompileProg_correct interp transform { source with clock } sourceLast sourceEnv config outputConfig
      evalConfig decs flatDecs result
      (factoredPrecondition1_changeClock interp transform source sourceEnv config evalConfig decs clock precondition)
      compiled sourceRun sourceSafe
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

/-- Match-row result in existential form, over the preliminary factored
relations and the compiled-row safety premise. -/
theorem factoredCompileMatch {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source sourceLast : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN)
    (traces : List BackendCommon.Tra) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (value errorValue : Value) (flatValue flatError : FlatSem.Value) (rows : List (Pat × AstHOL.Exp))
    (result : Result (List Value) Value)
    (sourceRun : EvaluateHOL.evaluateMatch source sourceEnv value rows errorValue = (sourceLast, result))
    (envRel : FactoredEnvAllRel genv compMap sourceEnv flatEnv locals)
    (tracesLen : traces.length = locals.length)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (valueRel : ValueRel genv value flatValue) (errorRel : ValueRel genv errorValue flatError)
    (flatSafe : FlatSem.pmatchRows (compilePes trace { compMap with v := bindLocals traces locals compMap.v } rows)
      flat flatValue ≠ .typeError) (safe : result ≠ .err (.abort .typeError)) :
    ∃ finalFlat flatResult nextGenv,
      flatEvaluateMatch flatEnv flat flatValue flatError
        (compilePes trace { compMap with v := bindLocals traces locals compMap.v } rows) = (finalFlat, flatResult) ∧
      EvalResultRel nextGenv result flatResult ∧ StateRel nextGenv sourceLast finalFlat ∧
      (match result with
       | .err (.abort _) => True
       | _ => GlobalGrowth genv nextGenv ∧
           factoredInvariant interp transform gen nextGenv (start, finish, other) sourceLast finalFlat ∧
           envGenRel gen sourceLast.evalState ∧ oracForwardRel interp source.evalState sourceLast.evalState) := by
  have sourceSafe : ∀ last, EvaluateHOL.evaluateMatch source sourceEnv value rows errorValue ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    rw [sourceRun] at bad
    exact safe (Prod.mk.inj bad).2
  obtain ⟨nextGenv, simulation, post⟩ := factoredEvaluateMatch_envAll interp transform genv start finish other
    source flat sourceEnv flatEnv locals traces trace compMap gen envRel tracesLen invariant generation
    value errorValue flatValue flatError valueRel errorRel rows flatSafe sourceSafe
  generalize flatRun : flatEvaluateMatch flatEnv flat flatValue flatError
    (compilePes trace { compMap with v := bindLocals traces locals compMap.v } rows) = flatPair at simulation post
  obtain ⟨finalFlat, flatResult⟩ := flatPair
  simp only [sourceRun] at simulation
  refine ⟨finalFlat, flatResult, nextGenv, rfl, simulation.1, simulation.2, ?_⟩
  cases result with
  | val values => simpa only [sourceRun] using post
  | err error =>
    cases error with
    | abort _ => trivial
    | raise _ => simpa only [sourceRun] using post

end Flapjack.Compiler.Backend.SourceToFlat
