import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalControl

/-! Argument-list simulation in arbitrary related local environments. The
factored relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

private theorem sourceEvaluate_cons {F : Type} (source : State F) (env : SemEnv Value)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp) :
    EvaluateHOL.evaluate source env (first :: second :: rest) =
      let head := EvaluateHOL.evaluate source env [first]
      match head.2 with
      | .err error => (head.1, .err error)
      | .val values =>
        let tail := EvaluateHOL.evaluate head.1 env (second :: rest)
        match tail.2 with
        | .err error => (tail.1, .err error)
        | .val values' => (tail.1, .val (EvaluateHOL.headValue values :: values')) := by
  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source env [first] []).1]
  rfl

/-- Compose local expression induction hypotheses over an arbitrary list. -/
theorem localEnvListStep_of_each {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → LocalEnvIH (F := F) interp transform expr) :
    ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
      (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
      (sourceLocal : Namespace ModN VarN Value) (flatEnv : FlatSem.Environment FlatSem.Value)
      (traces : List BackendCommon.Tra) (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore),
      EnvRel genv sourceLocal flatEnv.v →
      GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv →
      traces.length = flatEnv.v.length →
      factoredInvariant interp transform gen genv (start, finish, other) source flat →
      envGenRel gen source.evalState →
      (∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsAppend sourceLocal baseEnv.v } expressions ≠
        (last, .err (.abort .typeError))) →
      LocalExpressionListStep interp transform genv start finish other source flat
        { baseEnv with v := nsAppend sourceLocal baseEnv.v } flatEnv trace
        { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } gen expressions := by
  induction expressions with
  | nil =>
    intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen _ _ _ invariant generation _
    exact localExpressionListStep_empty interp transform genv start finish other source flat _ _ trace _ gen
      invariant generation
  | cons first rest ih =>
    intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
    let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
    let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
    cases rest with
    | nil =>
      apply localExpressionListStep_singleton
      exact each first (by simp) genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
        localRel envInv tracesLen invariant generation safe
    | cons second tail =>
      have headSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        change EvaluateHOL.evaluate source sourceEnv (first :: second :: tail) = _
        simp only [sourceEvaluate_cons, bad]
      have headStep := each first (by simp) genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
        localRel envInv tracesLen invariant generation headSafe
      change LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace
        compMap gen (first :: second :: tail)
      apply localExpressionListStep_cons interp transform genv start finish other source flat sourceEnv flatEnv trace
        compMap gen first second tail headStep
      intro middleGenv middleSource middleFlat headValue headRun growth middleInvariant middleGeneration
      have tailSafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv (second :: tail) ≠
          (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        change EvaluateHOL.evaluate source sourceEnv (first :: second :: tail) = _
        simp only [sourceEvaluate_cons, headRun, bad]
      apply ih
      · intro expr member
        exact each expr (List.mem_cons_of_mem _ member)
      · exact envRel_growth genv middleGenv growth sourceLocal flatEnv.v localRel
      · exact globalEnvInv_growth genv middleGenv growth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
      · exact tracesLen
      · exact middleInvariant
      · exact middleGeneration
      · exact tailSafe


/-- Compose localEnvIH_tuple over arbitrary related local environments. -/
theorem localEnvIH_tuple {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvIH (F := F) interp transform expr) :
    LocalEnvIH (F := F) interp transform (.con none args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.con none args)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.con none args] = _
    simp [EvaluateHOL.evaluate, doConCheck, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := localEnvListStep_of_each interp transform args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen localRel envInv tracesLen invariant generation argsSafe
  refine ⟨nextGenv, exprSim_tuple nextGenv compMap trace sourceEnv flatEnv source flat args argsSim, ?_⟩
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post ⊢
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at argsSim post ⊢
  obtain ⟨flatNext, flatResult⟩ := flatResult
  obtain ⟨resultRel, _⟩ := argsSim
  cases resultRel with
  | abort error =>
    simp [EvaluateHOL.evaluate, doConCheck, sourceRun]
  | raise related =>
    simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, doConCheck, sourceRun, flatRun] using post
  | value related =>
    simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, doConCheck, buildConv, sourceRun, flatRun] using post


/-- Compose localEnvIH_constructor over arbitrary related local environments. -/
theorem localEnvIH_constructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (id : Ident ModN ConN) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvIH (F := F) interp transform expr) :
    LocalEnvIH (F := F) interp transform (.con (some id) args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.con (some id) args)
  have check : doConCheck sourceEnv.c (some id) args.length = true := by
    cases h : doConCheck sourceEnv.c (some id) args.length with
    | true => rfl
    | false =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.con (some id) args] =
          (source, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, h, EvaluateHOL.typeError]
      exact False.elim (safe source bad)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.con (some id) args] = _
    simp [EvaluateHOL.evaluate, check, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := localEnvListStep_of_each interp transform args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen localRel envInv tracesLen invariant generation argsSafe
  have sim : ExprSim nextGenv compMap trace sourceEnv flatEnv source flat (.con (some id) args) := by
    generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = result at post
    obtain ⟨nextSource, result⟩ := result
    cases result with
    | err error =>
      cases error with
      | abort abort =>
        exact exprSim_constructor_abort nextGenv compMap trace sourceEnv flatEnv source flat (some id) args
          check argsSim nextSource abort sourceRun
      | raise value =>
        have growth : GlobalGrowth genv nextGenv := post.1
        have nextInv := globalEnvInv_growth genv nextGenv growth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
        cases lookup : nsLookup sourceEnv.c id with
        | none => simp [doConCheck, lookup] at check
        | some entry =>
          obtain ⟨arity, stamp⟩ := entry
          have same : args.length = arity := by simpa [doConCheck, lookup] using check
          subst arity
          cases nextInv with
          | intro _ _ _ _ constructors =>
            obtain ⟨cn, group, compiled, stampLookup, _⟩ := constructors id args.length stamp lookup
            exact exprSim_constructor_local_valid nextGenv compMap trace sourceEnv flatEnv source flat id args stamp
              lookup ⟨cn, group, compiled, stampLookup⟩ argsSim
    | val values =>
      have growth : GlobalGrowth genv nextGenv := post.1
      have nextInv := globalEnvInv_growth genv nextGenv growth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
      cases lookup : nsLookup sourceEnv.c id with
      | none => simp [doConCheck, lookup] at check
      | some entry =>
        obtain ⟨arity, stamp⟩ := entry
        have same : args.length = arity := by simpa [doConCheck, lookup] using check
        subst arity
        cases nextInv with
        | intro _ _ _ _ constructors =>
          obtain ⟨cn, group, compiled, stampLookup, _⟩ := constructors id args.length stamp lookup
          exact exprSim_constructor_local_valid nextGenv compMap trace sourceEnv flatEnv source flat id args stamp
            lookup ⟨cn, group, compiled, stampLookup⟩ argsSim
  refine ⟨nextGenv, sim, ?_⟩
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post ⊢
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at argsSim post ⊢
  obtain ⟨flatNext, flatResult⟩ := flatResult
  obtain ⟨resultRel, _⟩ := argsSim
  cases resultRel with
  | abort error => simp [EvaluateHOL.evaluate, check, sourceRun]
  | raise related => simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, check, sourceRun, flatRun] using post
  | @value sourceValues flatValues related =>
    cases built : buildConv sourceEnv.c (some id) sourceValues.reverse with
    | none =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.con (some id) args] =
          (sourceNext, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, check, sourceRun, built, EvaluateHOL.typeError]
      exact False.elim (safe sourceNext bad)
    | some value =>
      simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, check, sourceRun, flatRun, built] using post


/-- Covered expressions can combine tuples and named constructors with nested bindings and control flow. -/
inductive LocalEnvConstructorExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : LocalEnvControlExpression expr → LocalEnvConstructorExpression expr
  | tuple (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvConstructorExpression expr) →
      LocalEnvConstructorExpression (.con none args)
  | constructor (id : Ident ModN ConN) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → LocalEnvConstructorExpression expr) → LocalEnvConstructorExpression (.con (some id) args)
  | letNamed (name : VarN) (first body : AstHOL.Exp) : LocalEnvConstructorExpression first →
      LocalEnvConstructorExpression body → LocalEnvConstructorExpression (.let_ (some name) first body)
  | letAnonymous (first body : AstHOL.Exp) : LocalEnvConstructorExpression first → LocalEnvConstructorExpression body →
      LocalEnvConstructorExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : LocalEnvConstructorExpression cond → LocalEnvConstructorExpression yes →
      LocalEnvConstructorExpression no → LocalEnvConstructorExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : LocalEnvConstructorExpression left → LocalEnvConstructorExpression right →
      LocalEnvConstructorExpression (.log op left right)
  | raise_ (body : AstHOL.Exp) : LocalEnvConstructorExpression body → LocalEnvConstructorExpression (.raise body)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : LocalEnvConstructorExpression expr → LocalEnvConstructorExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : LocalEnvConstructorExpression expr →
      LocalEnvConstructorExpression (.lannot expr loc)

/-- Covered expressions satisfy the preliminary arbitrary-local hypothesis;
the relations remain pending HOL correspondence review. -/
theorem localEnvIH_constructorTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : LocalEnvConstructorExpression expr) : LocalEnvIH (F := F) interp transform expr := by
  induction covered with
  | base expr covered => exact localEnvIH_controlTree interp transform expr covered
  | tuple args _ ih => exact localEnvIH_tuple interp transform args ih
  | constructor id args _ ih => exact localEnvIH_constructor interp transform id args ih
  | letNamed name first body _ _ firstIH bodyIH => exact localEnvIH_let_named interp transform name first body firstIH bodyIH
  | letAnonymous first body _ _ firstIH bodyIH => exact localEnvIH_let_anonymous interp transform first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact localEnvIH_if interp transform cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact localEnvIH_log interp transform op left right leftIH rightIH
  | raise_ body _ ih => exact localEnvIH_raise interp transform body ih
  | tannot expr typ _ ih => exact localEnvIH_tannot interp transform expr typ ih
  | lannot expr loc _ ih => exact localEnvIH_lannot interp transform expr loc ih


end Flapjack.Compiler.Backend.SourceToFlat
