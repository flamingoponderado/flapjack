import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalPrimitive

/-! Array primitive simulation in arbitrary related local environments.
These factored relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Fixed array allocation evaluates its fields right-to-left, restores the
source field order, and preserves the reserved flat store entry. -/
theorem localEnvIH_aallocFixed {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvIH (F := F) interp transform expr) :
    LocalEnvIH (F := F) interp transform (.app .aallocFixed args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.app .aallocFixed args)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aallocFixed args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := localEnvListStep_of_each interp transform args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat
    baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    obtain ⟨sourceApp, flatApp, locationRel, stateRel, reserved⟩ :=
      aallocFixed_related nextGenv nextSource nextFlat states sourceValues.reverse flatValues.reverse
        (List.rel_reverse valuesRel)
    have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
      nextSource nextFlat (storeAlloc (.varray sourceValues.reverse) nextSource.refs).1
      (storeAlloc (.varray flatValues.reverse) nextFlat.refs).1 nextInvariant stateRel reserved
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      simp [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
        FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult]
      exact ⟨.value (.cons locationRel .nil), stateRel⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      simpa [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
        FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult] using
        And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))

/-- Covered expressions combine fixed array allocation with the previously covered forms. -/
inductive LocalEnvArrayExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : LocalEnvPrimitiveExpression expr → LocalEnvArrayExpression expr
  | arrayFixed (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvArrayExpression expr) →
      LocalEnvArrayExpression (.app .aallocFixed args)
  | tuple (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvArrayExpression expr) →
      LocalEnvArrayExpression (.con none args)
  | constructor (id : Ident ModN ConN) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → LocalEnvArrayExpression expr) → LocalEnvArrayExpression (.con (some id) args)
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) :
      LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app (.test test typ) [left, right])
  | equality (left right : AstHOL.Exp) : LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app .equality [left, right])
  | integerArith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app (.arith action .intT) [left, right])
  | word8Arith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app (.arith action (.wordT .w8)) [left, right])
  | word64Arith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app (.arith action (.wordT .w64)) [left, right])
  | word8Shift (shift : Shift) (amount : Nat) (body : AstHOL.Exp) : LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.app (.shift .w8 shift amount) [body])
  | word64Shift (shift : Shift) (amount : Nat) (body : AstHOL.Exp) : LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.app (.shift .w64 shift amount) [body])
  | conversion (fromType toType : PrimType) (body : AstHOL.Exp) : LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.app (.fromTo fromType toType) [body])
  | ref_ (body : AstHOL.Exp) : LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.app .opref [body])
  | assign (left right : AstHOL.Exp) : LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app .opassign [left, right])
  | deref (body : AstHOL.Exp) : LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.app .opderef [body])
  | letNamed (name : VarN) (first body : AstHOL.Exp) : LocalEnvArrayExpression first →
      LocalEnvArrayExpression body → LocalEnvArrayExpression (.let_ (some name) first body)
  | letAnonymous (first body : AstHOL.Exp) : LocalEnvArrayExpression first → LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : LocalEnvArrayExpression cond → LocalEnvArrayExpression yes →
      LocalEnvArrayExpression no → LocalEnvArrayExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.log op left right)
  | raise_ (body : AstHOL.Exp) : LocalEnvArrayExpression body → LocalEnvArrayExpression (.raise body)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : LocalEnvArrayExpression expr → LocalEnvArrayExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : LocalEnvArrayExpression expr →
      LocalEnvArrayExpression (.lannot expr loc)

/-- Covered expressions satisfy the preliminary arbitrary-local hypothesis;
the relations remain pending HOL correspondence review. -/
theorem localEnvIH_arrayTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : LocalEnvArrayExpression expr) : LocalEnvIH (F := F) interp transform expr := by
  induction covered with
  | base expr covered => exact localEnvIH_primitiveTree interp transform expr covered
  | arrayFixed args _ ih => exact localEnvIH_aallocFixed interp transform args ih
  | tuple args _ ih => exact localEnvIH_tuple interp transform args ih
  | constructor id args _ ih => exact localEnvIH_constructor interp transform id args ih
  | test test typ left right _ _ leftIH rightIH => exact localEnvIH_test interp transform test typ left right leftIH rightIH
  | equality left right _ _ leftIH rightIH => exact localEnvIH_equality interp transform left right leftIH rightIH
  | integerArith action left right _ _ leftIH rightIH =>
    exact localEnvIH_integerArith interp transform action left right leftIH rightIH
  | word8Arith action left right _ _ leftIH rightIH =>
    exact localEnvIH_word8Arith interp transform action left right leftIH rightIH
  | word64Arith action left right _ _ leftIH rightIH =>
    exact localEnvIH_word64Arith interp transform action left right leftIH rightIH
  | word8Shift shift amount body _ ih => exact localEnvIH_word8Shift interp transform body shift amount ih
  | word64Shift shift amount body _ ih => exact localEnvIH_word64Shift interp transform body shift amount ih
  | conversion fromType toType body _ ih =>
    exact localEnvIH_conversion interp transform body fromType toType ih
  | ref_ body _ ih => exact localEnvIH_opref interp transform body ih
  | assign left right _ _ leftIH rightIH => exact localEnvIH_opassign interp transform left right leftIH rightIH
  | deref body _ ih => exact localEnvIH_opderef interp transform body ih
  | letNamed name first body _ _ firstIH bodyIH => exact localEnvIH_let_named interp transform name first body firstIH bodyIH
  | letAnonymous first body _ _ firstIH bodyIH => exact localEnvIH_let_anonymous interp transform first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact localEnvIH_if interp transform cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact localEnvIH_log interp transform op left right leftIH rightIH
  | raise_ body _ ih => exact localEnvIH_raise interp transform body ih
  | tannot expr typ _ ih => exact localEnvIH_tannot interp transform expr typ ih
  | lannot expr loc _ ih => exact localEnvIH_lannot interp transform expr loc ih




end Flapjack.Compiler.Backend.SourceToFlat
