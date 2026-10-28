import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundList

/-! Named constructor simulation under a local binding. The factored
relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A constructor lookup simulation needs the constructor component of the
global invariant; local variable bindings leave that component unchanged. -/
theorem exprSim_constructor_local_valid {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : State F) (flatState : FlatSem.State C F)
    (id : Ident ModN ConN) (args : List AstHOL.Exp) (stamp : Stamp)
    (sourceLookup : nsLookup sourceEnv.c id = some (args.length, stamp))
    (mapped : ∃ cn group, nsLookup compMap.c id = some (cn, group) ∧
      genv.c.lookup ((cn, group.map Prod.fst), args.length) = some stamp)
    (argsSim : ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState args.reverse) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.con (some id) args) := by
  obtain ⟨cn, group, compiledLookup, stampLookup⟩ := mapped
  have compiledCtor : typeGroupIdType (some (cn, group)) = some (cn, group.map Prod.fst) := by
    cases group with
    | none => rfl
    | some pair => cases pair; rfl
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv args.reverse with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at argsSim
    cases flatRun : FlatSem.evaluate flatEnv flatState (compileExps trace compMap args).reverse with
    | mk flatNext flatResult =>
      rw [flatRun] at argsSim
      obtain ⟨related, nextRel⟩ := argsSim
      cases related with
      | value valuesRel =>
        have lengthEq := EvaluateProps.evaluateLengthFull sourceState sourceNext sourceEnv args.reverse _ sourceRun
        simp only [List.length_reverse] at lengthEq
        unfold ExprSim
        rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
        simp only [doConCheck, sourceLookup, beq_self_eq_true, ↓reduceIte,
          Option.bind_some, compiledLookup, compiledCtor, sourceRun, flatRun, buildConv]
        apply And.intro _ nextRel
        apply ResultRel.value
        apply List.Forall₂.cons _ List.Forall₂.nil
        apply valueRel_constructor genv stamp (cn, group.map Prod.fst)
        · exact List.rel_reverse valuesRel
        · simpa [List.length_reverse, lengthEq] using stampLookup
      | raise valueRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
        simp only [doConCheck, sourceLookup, beq_self_eq_true, ↓reduceIte, sourceRun, flatRun]
        exact ⟨.raise valueRel, nextRel⟩
      | abort error =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
        simp only [doConCheck, sourceLookup, beq_self_eq_true, ↓reduceIte, sourceRun, flatRun]
        exact ⟨.abort error, nextRel⟩


/-- Safe named constructors compose local argument hypotheses. Their tags
come from the global invariant, whose constructor fields survive a local bind. -/
theorem boundLocalIH_constructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (id : Ident ModN ConN) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → BoundLocalIH (F := F) interp transform name expr) :
    BoundLocalIH (F := F) interp transform name (.con (some id) args) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related envInv invariant generation safe
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
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
  obtain ⟨nextGenv, argsSim, post⟩ := boundLocalListStep_of_each interp transform name args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv
    trace baseMap gen value flatValue related envInv invariant generation argsSafe
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
        have nextInv := globalEnvInv_growth genv nextGenv growth baseMap (fun _ => False) baseEnv envInv
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
      have nextInv := globalEnvInv_growth genv nextGenv growth baseMap (fun _ => False) baseEnv envInv
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

/-- Local expressions with named constructors and recursively covered fields. -/
inductive BoundConstructorExpression (name : VarN) : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : BoundTupleExpression name expr → BoundConstructorExpression name expr
  | constructor (id : Ident ModN ConN) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → BoundConstructorExpression name expr) →
      BoundConstructorExpression name (.con (some id) args)
  | tuple (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → BoundConstructorExpression name expr) →
      BoundConstructorExpression name (.con none args)
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) :
      BoundConstructorExpression name left → BoundConstructorExpression name right →
      BoundConstructorExpression name (.app (.test test typ) [left, right])
  | equality (left right : AstHOL.Exp) : BoundConstructorExpression name left → BoundConstructorExpression name right →
      BoundConstructorExpression name (.app .equality [left, right])
  | integerArith (action : Arith) (left right : AstHOL.Exp) :
      BoundConstructorExpression name left → BoundConstructorExpression name right →
      BoundConstructorExpression name (.app (.arith action .intT) [left, right])
  | log (op : Lop) (left right : AstHOL.Exp) : BoundConstructorExpression name left →
      BoundConstructorExpression name right → BoundConstructorExpression name (.log op left right)
  | if_ (cond yes no : AstHOL.Exp) : BoundConstructorExpression name cond → BoundConstructorExpression name yes →
      BoundConstructorExpression name no → BoundConstructorExpression name (.if_ cond yes no)

/-- Constructor-covered expressions satisfy the preliminary local induction
hypothesis; correspondence of its relations with HOL remains unreviewed. -/
theorem boundLocalIH_constructorTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (expr : AstHOL.Exp) (covered : BoundConstructorExpression name expr) :
    BoundLocalIH (F := F) interp transform name expr := by
  induction covered with
  | base expr covered => exact boundLocalIH_tupleTree interp transform name expr covered
  | constructor id args _ ih => exact boundLocalIH_constructor interp transform name id args ih
  | tuple args _ ih => exact boundLocalIH_tuple interp transform name args ih
  | test test typ left right _ _ leftIH rightIH =>
    exact boundLocalIH_test interp transform name test typ left right leftIH rightIH
  | equality left right _ _ leftIH rightIH => exact boundLocalIH_equality interp transform name left right leftIH rightIH
  | integerArith action left right _ _ leftIH rightIH =>
    exact boundLocalIH_integerArith interp transform name action left right leftIH rightIH
  | log op left right _ _ leftIH rightIH => exact boundLocalIH_log interp transform name op left right leftIH rightIH
  | if_ cond yes no _ _ _ condIH yesIH noIH =>
    exact boundLocalIH_if interp transform name cond yes no condIH yesIH noIH

/-- Named bindings with constructor-covered local bodies satisfy the
preliminary declaration-expression hypothesis. -/
theorem factoredExpressionIH_let_named_constructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first body : AstHOL.Exp) (covered : BoundConstructorExpression name body)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first body) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first body firstIH
  exact boundLocalIH_constructorTree interp transform name body covered

end Flapjack.Compiler.Backend.SourceToFlat
