import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBounded
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalPrimitive

/-! Clock-bounded primitive simulation over preliminary source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A simple primitive that rejects all argument lists of this length still
simulates errors raised while evaluating its arguments. The rejection premise
is discharged separately for each malformed operator and arity. -/
theorem localEnvBounded_rejectedSimple {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (args : List AstHOL.Exp)
    (simple : getOpClass op = .simple)
    (notEmpty : op ≠ .aallocEmpty) (notEval : op ≠ .eval) (notEnvId : op ≠ .envId)
    (rejects : ∀ (state : State F) values, values.length = args.length →
      doApp (state.refs, state.ffi) op values = none)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app op args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at argsSim post
  obtain ⟨flatNext, flatResult⟩ := flatResult
  obtain ⟨resultRel, states⟩ := argsSim
  cases resultRel with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      trivial
  | raise related =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise related, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues related =>
    have length := EvaluateProps.evaluateLengthFull source sourceNext sourceEnv args.reverse sourceValues sourceRun
    have rejected : doApp (sourceNext.refs, sourceNext.ffi) op sourceValues.reverse = none :=
      rejects sourceNext sourceValues.reverse (by simpa using length)
    apply False.elim
    apply safe sourceNext
    change EvaluateHOL.evaluate source sourceEnv [.app op args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
    simp [simple, rejected, EvaluateHOL.typeError]

/-- Conversions reject every non-unary application after evaluating its
arguments. Argument errors are still propagated by the enclosing expression. -/
theorem localEnvBounded_conversion_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (fromType toType : PrimType) (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.fromTo fromType toType) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.fromTo fromType toType) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 1 := by simpa [length] using badArity
  cases values with
  | nil => cases fromType <;> cases toType <;> (try cases ‹WordSize›) <;> (try cases ‹WordSize›) <;>
      simp [doApp, doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp at bad
    | cons second rest =>
      cases fromType <;> cases toType <;> (try cases ‹WordSize›) <;> (try cases ‹WordSize›) <;>
        simp [doApp, doAppNumericCore]

/-- Shifts reject non-unary argument lists after evaluating their operands. -/
theorem localEnvBounded_shift_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (size : WordSize) (shift : Shift) (amount : Nat) (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.shift size shift amount) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.shift size shift amount) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 1 := by simpa [length] using badArity
  cases values with
  | nil => cases size <;> simp [doApp, doAppNumericCore, doAppBasic]
  | cons first rest =>
    cases rest with
    | nil => simp at bad
    | cons second rest => cases size <;> simp [doApp, doAppNumericCore, doAppBasic]

/-- Equality and primitive tests reject non-binary argument lists after their
operands have been evaluated. -/
theorem localEnvBounded_comparison_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (test : Option (Test × PrimType)) (args : List AstHOL.Exp) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit
      (.app (match test with | none => .equality | some (test, typ) => .test test typ) args) := by
  let op := match test with | none => Op.equality | some (test, typ) => Op.test test typ
  change LocalEnvBoundedIH (F := F) interp transform limit (.app op args)
  have simple : getOpClass op = .simple := by cases test <;> simp [op, getOpClass]
  have notEmpty : op ≠ .aallocEmpty := by cases test <;> simp [op]
  have notEval : op ≠ .eval := by cases test <;> simp [op]
  have notEnvId : op ≠ .envId := by cases test <;> simp [op]
  apply localEnvBounded_rejectedSimple interp transform limit op args simple notEmpty notEval notEnvId _ each
  intro state values length
  have bad : values.length ≠ 2 := by simpa [length] using badArity
  cases values with
  | nil => cases test <;> simp [op, doApp, doAppNumericCore, doAppBasic]
  | cons first rest =>
    cases rest with
    | nil => cases test <;> simp [op, doApp, doAppNumericCore, doAppBasic]
    | cons second rest =>
      cases rest with
      | nil => simp at bad
      | cons third rest => cases test <;> simp [op, doApp, doAppNumericCore, doAppBasic]

/-- Arithmetic operators take at least one and at most three operands. This
case preserves argument errors even when the operand count is outside that
range. More precise arities depend on the primitive type. -/
theorem localEnvBounded_arith_extremeArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (typ : PrimType) (args : List AstHOL.Exp)
    (badArity : args.length = 0 ∨ 3 < args.length)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action typ) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.arith action typ) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length = 0 ∨ 3 < values.length := by simpa [length] using badArity
  cases values with
  | nil => cases typ <;> (try cases ‹WordSize›) <;> cases action <;>
      simp [doApp, doAppNumericCore, floatArith]
  | cons first rest =>
    cases rest with
    | nil => simp at bad
    | cons second rest =>
      cases rest with
      | nil => simp at bad
      | cons third rest =>
        cases rest with
        | nil => simp at bad
        | cons fourth rest =>
          cases typ <;> (try cases ‹WordSize›) <;> cases action <;>
            simp [doApp, doAppNumericCore, floatArith]

/-- Integer and word arithmetic reject every non-binary operand list. -/
theorem localEnvBounded_intWordArith_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (size : Option WordSize) (args : List AstHOL.Exp) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit
      (.app (.arith action (match size with | none => .intT | some w => .wordT w)) args) := by
  let typ := match size with | none => PrimType.intT | some w => PrimType.wordT w
  change LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action typ) args)
  apply localEnvBounded_rejectedSimple interp transform limit (.arith action typ) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 2 := by simpa [length] using badArity
  cases values with
  | nil => cases size <;> simp [typ, doApp, doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => cases size <;> simp [typ, doApp, doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at bad
      | cons third rest => cases size <;> simp [typ, doApp, doAppNumericCore]

/-- Boolean arithmetic rejects every non-unary operand list. -/
theorem localEnvBounded_boolArith_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action .boolT) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.arith action .boolT) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 1 := by simpa [length] using badArity
  cases values with
  | nil => cases action <;> simp [doApp, doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp at bad
    | cons second rest => cases action <;> simp [doApp, doAppNumericCore]

/-- Only fused multiply-add accepts three floating-point operands. -/
theorem localEnvBounded_floatTernary_nonFma {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (args : List AstHOL.Exp) (notFma : action ≠ .fma) (arity : args.length = 3)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action .float64T) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.arith action .float64T) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have count : values.length = 3 := by simpa [length] using arity
  cases values with
  | nil => simp at count
  | cons first rest =>
    cases rest with
    | nil => simp at count
    | cons second rest =>
      cases rest with
      | nil => simp at count
      | cons third rest =>
        cases rest with
        | cons fourth rest => simp at count
        | nil => cases action <;> simp [doApp, floatArith] at notFma ⊢

/-- Character and string arithmetic, and Boolean arithmetic other than
negation, reject every operand list after evaluating its expressions. -/
theorem localEnvBounded_arith_rejectedType {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (typ : PrimType) (args : List AstHOL.Exp)
    (unsupported : typ = .charT ∨ typ = .strT ∨ (typ = .boolT ∧ action ≠ .not))
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action typ) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.arith action typ) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values _
  rcases unsupported with rfl | rfl | ⟨rfl, notNot⟩
  · simp [doApp, doAppNumericCore]
  · simp [doApp, doAppNumericCore]
  · cases action <;> simp [doApp, doAppNumericCore] at notNot ⊢

/-- The ordinary unary primitives used by references, strings, vectors, and
arrays. This predicate is bookkeeping for the factored simulation. -/
def UnaryBasicOp (op : Op) : Prop :=
  op = .opref ∨ op = .opderef ∨ op = .aw8length ∨ op = .implode ∨ op = .explode ∨
  op = .strlen ∨ op = .strcat ∨ op = .vfromList ∨ op = .vlength ∨ op = .alength

/-- Ordinary unary primitives reject operand lists of any other length. -/
theorem localEnvBounded_unaryBasic_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (args : List AstHOL.Exp) (unary : UnaryBasicOp op) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  rcases unary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply localEnvBounded_rejectedSimple interp transform limit _ args rfl (by simp) (by simp) (by simp) _ each
  all_goals intro state values length
  all_goals have bad : values.length ≠ 1 := by simpa [length] using badArity
  all_goals cases values with
    | nil => simp [doApp, doAppNumericCore, doAppBasic]
    | cons first rest =>
      cases rest with
      | nil => simp at bad
      | cons second rest => simp [doApp, doAppNumericCore, doAppBasic]

/-- Ordinary binary reference, collection, and configuration primitives. -/
def BinaryBasicOp (op : Op) : Prop :=
  op = .opassign ∨ op = .listAppend ∨ op = .aw8alloc ∨ op = .aw8sub ∨ op = .aw8subUnsafe ∨
  op = .xorAw8StrUnsafe ∨ op = .strsub ∨ op = .vsub ∨ op = .vsubUnsafe ∨ op = .aalloc ∨
  op = .asub ∨ op = .asubUnsafe ∨ op = .configGC

/-- Ordinary binary primitives reject operand lists of any other length. -/
theorem localEnvBounded_binaryBasic_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (args : List AstHOL.Exp) (binary : BinaryBasicOp op) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  rcases binary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply localEnvBounded_rejectedSimple interp transform limit _ args rfl (by simp) (by simp) (by simp) _ each
  all_goals intro state values length
  all_goals have bad : values.length ≠ 2 := by simpa [length] using badArity
  all_goals cases values with
    | nil => simp [doApp, doAppNumericCore, doAppBasic]
    | cons first rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic]
      | cons second rest =>
        cases rest with
        | nil => simp at bad
        | cons third rest => simp [doApp, doAppNumericCore, doAppBasic]

/-- Ordinary ternary update and slicing primitives. -/
def TernaryBasicOp (op : Op) : Prop :=
  op = .aupdate ∨ op = .aupdateUnsafe ∨ op = .aw8update ∨ op = .aw8updateUnsafe ∨
  op = .copyStrStr ∨ op = .copyAw8Str

/-- Ordinary ternary primitives reject operand lists of any other length. -/
theorem localEnvBounded_ternaryBasic_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (args : List AstHOL.Exp) (ternary : TernaryBasicOp op) (badArity : args.length ≠ 3)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  rcases ternary with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply localEnvBounded_rejectedSimple interp transform limit _ args rfl (by simp) (by simp) (by simp) _ each
  all_goals intro state values length
  all_goals have bad : values.length ≠ 3 := by simpa [length] using badArity
  all_goals cases values with
    | nil => simp [doApp, doAppNumericCore, doAppBasic]
    | cons first rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic]
      | cons second rest =>
        cases rest with
        | nil => simp [doApp, doAppNumericCore, doAppBasic]
        | cons third rest =>
          cases rest with
          | nil => simp at bad
          | cons fourth rest => simp [doApp, doAppNumericCore, doAppBasic]

/-- The two five-operand byte-copy primitives. -/
def FiveArgBasicOp (op : Op) : Prop := op = .copyStrAw8 ∨ op = .copyAw8Aw8

/-- Five-operand byte copies reject operand lists of any other length. -/
theorem localEnvBounded_fiveArgBasic_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (args : List AstHOL.Exp) (copy : FiveArgBasicOp op) (badArity : args.length ≠ 5)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  rcases copy with rfl | rfl
  all_goals apply localEnvBounded_rejectedSimple interp transform limit _ args rfl (by simp) (by simp) (by simp) _ each
  all_goals intro state values length
  all_goals have bad : values.length ≠ 5 := by simpa [length] using badArity
  all_goals cases values with
    | nil => simp [doApp, doAppNumericCore, doAppBasic]
    | cons first rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic]
      | cons second rest =>
        cases rest with
        | nil => simp [doApp, doAppNumericCore, doAppBasic]
        | cons third rest =>
          cases rest with
          | nil => simp [doApp, doAppNumericCore, doAppBasic]
          | cons fourth rest =>
            cases rest with
            | nil => simp [doApp, doAppNumericCore, doAppBasic]
            | cons fifth rest =>
              cases rest with
              | nil => simp at bad
              | cons sixth rest => simp [doApp, doAppNumericCore, doAppBasic]

/-- Foreign calls reject non-binary operand lists after evaluating them. -/
theorem localEnvBounded_ffi_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (name : Basis.Pure.MlString.MlString) (args : List AstHOL.Exp) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.ffi name) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.ffi name) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 2 := by simpa [length] using badArity
  cases values with
  | nil => simp [doApp, doAppNumericCore, doAppBasic]
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic]
    | cons second rest =>
      cases rest with
      | nil => simp at bad
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic]

/-- Compose localEnvBounded_tuple over arbitrary related local environments. -/
theorem localEnvBounded_tuple {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.con none args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.con none args)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.con none args] = _
    simp [EvaluateHOL.evaluate, doConCheck, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
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


/-- Compose localEnvBounded_constructor over arbitrary related local environments. -/
theorem localEnvBounded_constructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (id : Ident ModN ConN) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.con (some id) args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
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
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
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



/-- Compose test operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_test {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (test : Test) (typ : PrimType) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.test test typ) [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.test test typ) [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_test nextGenv compMap trace sourceEnv flatEnv source flat left right test typ
      nextInvariant.1 argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          cases comparison : SemanticPrimitivesHOL.doTest test typ sourceLeft sourceRight with
          | typeError =>
            apply False.elim
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, doApp, comparison, EvaluateHOL.typeError]
          | val b =>
            have flatComparison := doTest_related nextGenv nextInvariant.1 test typ sourceLeft sourceRight
              flatLeft flatRight b leftRel rightRel comparison
            refine ⟨nextGenv, exprSim_test nextGenv compMap trace sourceEnv flatEnv source flat left right test typ
              nextInvariant.1 argsSimCopy safe, ?_⟩
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flat
              [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, doApp, comparison, astOpToFlatOp, FlatSem.applyResult,
              FlatSem.doApp, FlatSem.doAppNumeric, flatComparison, EvaluateHOL.listResult] using
              And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- Compose equality operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_equality {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .equality [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .equality [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_equality nextGenv compMap trace sourceEnv flatEnv source flat left right
      nextInvariant.1 argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          cases comparison : SemanticPrimitivesHOL.doEq sourceLeft sourceRight with
          | typeError =>
            apply False.elim
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, doApp, doAppNumericCore, doAppBasic, comparison, EvaluateHOL.typeError]
          | val b =>
            have flatComparison := equality_preserved nextGenv nextInvariant.1 sourceLeft sourceRight
              flatLeft flatRight leftRel rightRel
            refine ⟨nextGenv, exprSim_equality nextGenv compMap trace sourceEnv flatEnv source flat left right
              nextInvariant.1 argsSimCopy safe, ?_⟩
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flat
              [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, comparison, astOpToFlatOp, FlatSem.applyResult,
              FlatSem.doApp, FlatSem.doAppNumeric, flatComparison, EvaluateHOL.listResult] using
              And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- Compose integerArith operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_integerArith {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action .intT) [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.arith action .intT) [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_integerArith nextGenv compMap trace sourceEnv flatEnv source flat left right action
      nextInvariant.1 argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) (.arith action .intT)
              [sourceLeft, sourceRight] ≠ none := by
            intro failed
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨leftInt, rightInt, operands⟩ := integerArith_operands nextSource action [sourceLeft, sourceRight] successful
          simp only [List.cons.injEq] at operands
          obtain ⟨rfl, rfl, _⟩ := operands
          have flatLeftEq := (valueRel_literal_iff nextGenv (.intLit leftInt) flatLeft).mp leftRel
          have flatRightEq := (valueRel_literal_iff nextGenv (.intLit rightInt) flatRight).mp rightRel
          subst flatLeft
          subst flatRight
          have primitive := integerArith_related nextGenv nextInvariant.1 nextSource nextFlat action leftInt rightInt
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) (.arith action .intT)
              [.litv (.intLit leftInt), .litv (.intLit rightInt)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppNumeric nextFlat (.arith action .intT)
                    [.litv (.intLit leftInt), .litv (.intLit rightInt)] with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | mk flatAfter flatResult =>
                      simp only [sourceApp, flatApp] at primitive
                      obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
                      refine ⟨nextGenv, exprSim_integerArith nextGenv compMap trace sourceEnv flatEnv source flat
                        left right action nextInvariant.1 argsSimCopy safe, ?_⟩
                      rw [EvaluateHOL.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
                      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                      rw [FlatSem.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(FlatSem.fixClock_evaluations flatEnv flat
                        [compileExp trace compMap right, compileExp trace compMap left]
                        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                        getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp, flatApp]
                      cases resultRel with
                      | value valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | raise valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | abort error => simp [EvaluateHOL.listResult]


/-- Compose word8Arith operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_word8Arith {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action (.wordT .w8)) [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.arith action (.wordT .w8)) [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.word8 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_word8Arith nextGenv compMap trace sourceEnv flatEnv source flat left right action
      argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.word8 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) (.arith action (.wordT .w8))
              [sourceLeft, sourceRight] ≠ none := by
            intro failed
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨leftWord, rightWord, operands⟩ := word8Arith_operands nextSource action [sourceLeft, sourceRight] successful
          simp only [List.cons.injEq] at operands
          obtain ⟨rfl, rfl, _⟩ := operands
          have flatLeftEq := (valueRel_literal_iff nextGenv (.word8 leftWord) flatLeft).mp leftRel
          have flatRightEq := (valueRel_literal_iff nextGenv (.word8 rightWord) flatRight).mp rightRel
          subst flatLeft
          subst flatRight
          have primitive := word8Arith_related nextGenv nextSource nextFlat action leftWord rightWord
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) (.arith action (.wordT .w8))
              [.litv (.word8 leftWord), .litv (.word8 rightWord)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppNumeric nextFlat (.arith action (.wordT .w8))
                    [.litv (.word8 leftWord), .litv (.word8 rightWord)] with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | mk flatAfter flatResult =>
                      simp only [sourceApp, flatApp] at primitive
                      obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
                      refine ⟨nextGenv, exprSim_word8Arith nextGenv compMap trace sourceEnv flatEnv source flat
                        left right action argsSimCopy safe, ?_⟩
                      rw [EvaluateHOL.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
                      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                      rw [FlatSem.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(FlatSem.fixClock_evaluations flatEnv flat
                        [compileExp trace compMap right, compileExp trace compMap left]
                        (FlatLang.Exp.lit .none (.word8 0)) []).1, flatRun]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                        getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp, flatApp]
                      cases resultRel with
                      | value valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | raise valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | abort error => simp [EvaluateHOL.listResult]


/-- Compose word64Arith operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_word64Arith {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action (.wordT .w64)) [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.arith action (.wordT .w64)) [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.word64 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_word64Arith nextGenv compMap trace sourceEnv flatEnv source flat left right action
      argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.word64 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) (.arith action (.wordT .w64))
              [sourceLeft, sourceRight] ≠ none := by
            intro failed
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨leftWord, rightWord, operands⟩ := word64Arith_operands nextSource action [sourceLeft, sourceRight] successful
          simp only [List.cons.injEq] at operands
          obtain ⟨rfl, rfl, _⟩ := operands
          have flatLeftEq := (valueRel_literal_iff nextGenv (.word64 leftWord) flatLeft).mp leftRel
          have flatRightEq := (valueRel_literal_iff nextGenv (.word64 rightWord) flatRight).mp rightRel
          subst flatLeft
          subst flatRight
          have primitive := word64Arith_related nextGenv nextSource nextFlat action leftWord rightWord
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) (.arith action (.wordT .w64))
              [.litv (.word64 leftWord), .litv (.word64 rightWord)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppNumeric nextFlat (.arith action (.wordT .w64))
                    [.litv (.word64 leftWord), .litv (.word64 rightWord)] with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | mk flatAfter flatResult =>
                      simp only [sourceApp, flatApp] at primitive
                      obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
                      refine ⟨nextGenv, exprSim_word64Arith nextGenv compMap trace sourceEnv flatEnv source flat
                        left right action argsSimCopy safe, ?_⟩
                      rw [EvaluateHOL.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
                      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                      rw [FlatSem.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(FlatSem.fixClock_evaluations flatEnv flat
                        [compileExp trace compMap right, compileExp trace compMap left]
                        (FlatLang.Exp.lit .none (.word64 0)) []).1, flatRun]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                        getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp, flatApp]
                      cases resultRel with
                      | value valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | raise valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | abort error => simp [EvaluateHOL.listResult]


/-- Binary floating-point arithmetic preserves the factored simulation. -/
theorem localEnvBounded_floatBinary {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action .float64T) [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.arith action .float64T) [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.float64 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_floatBinary nextGenv compMap trace sourceEnv flatEnv source flat left right action
      argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.float64 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) (.arith action .float64T)
              [sourceLeft, sourceRight] ≠ none := by
            intro failed
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨leftWord, rightWord, operands⟩ := floatBinary_operands nextSource action sourceLeft sourceRight successful
          simp only [List.cons.injEq] at operands
          obtain ⟨rfl, rfl, _⟩ := operands
          have flatLeftEq := (valueRel_literal_iff nextGenv (.float64 leftWord) flatLeft).mp leftRel
          have flatRightEq := (valueRel_literal_iff nextGenv (.float64 rightWord) flatRight).mp rightRel
          subst flatLeft
          subst flatRight
          have primitive := floatBinary_related nextGenv nextSource nextFlat action leftWord rightWord
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) (.arith action .float64T)
              [.litv (.float64 leftWord), .litv (.float64 rightWord)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppNumeric nextFlat (.arith action .float64T)
                    [.litv (.float64 leftWord), .litv (.float64 rightWord)] with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | mk flatAfter flatResult =>
                      simp only [sourceApp, flatApp] at primitive
                      obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
                      refine ⟨nextGenv, exprSim_floatBinary nextGenv compMap trace sourceEnv flatEnv source flat
                        left right action argsSimCopy safe, ?_⟩
                      rw [EvaluateHOL.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
                      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                      rw [FlatSem.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(FlatSem.fixClock_evaluations flatEnv flat
                        [compileExp trace compMap right, compileExp trace compMap left]
                        (FlatLang.Exp.lit .none (.float64 0)) []).1, flatRun]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                        getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp, flatApp]
                      cases resultRel with
                      | value valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | raise valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | abort error => simp [EvaluateHOL.listResult]


/-- Word8 shifts compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_word8Shift {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (shift : Shift) (amount : Nat)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.shift .w8 shift amount) [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.shift .w8 shift amount) [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  have bodySimCopy := bodySim
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, exprSim_word8Shift nextGenv compMap trace sourceEnv flatEnv source flat body shift amount bodySimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source nextSource sourceEnv body sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) (.shift .w8 shift amount) [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app (.shift .w8 shift amount) [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨word, rfl⟩ := word8Shift_operand nextSource shift amount operand successful
        have flatEq := (valueRel_literal_iff nextGenv (.word8 word) flatOperand).mp valueRel
        subst flatOperand
        obtain ⟨sourceApp, flatApp, resultRel⟩ := word8Shift_related nextGenv nextSource nextFlat shift amount word
        refine ⟨nextGenv, exprSim_word8Shift nextGenv compMap trace sourceEnv flatEnv source flat body shift amount bodySimCopy safe, ?_⟩
        rw [EvaluateHOL.evaluate]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
        simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
        rw [FlatSem.evaluate]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
          (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        simpa [getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp, flatApp, EvaluateHOL.listResult] using
          And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))

/-- Word64 shifts compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_word64Shift {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (shift : Shift) (amount : Nat)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.shift .w64 shift amount) [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.shift .w64 shift amount) [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  have bodySimCopy := bodySim
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, exprSim_word64Shift nextGenv compMap trace sourceEnv flatEnv source flat body shift amount bodySimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source nextSource sourceEnv body sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) (.shift .w64 shift amount) [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app (.shift .w64 shift amount) [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨word, rfl⟩ := word64Shift_operand nextSource shift amount operand successful
        have flatEq := (valueRel_literal_iff nextGenv (.word64 word) flatOperand).mp valueRel
        subst flatOperand
        obtain ⟨sourceApp, flatApp, resultRel⟩ := word64Shift_related nextGenv nextSource nextFlat shift amount word
        refine ⟨nextGenv, exprSim_word64Shift nextGenv compMap trace sourceEnv flatEnv source flat body shift amount bodySimCopy safe, ?_⟩
        rw [EvaluateHOL.evaluate]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
        simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
        rw [FlatSem.evaluate]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
          (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        simpa [getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp, flatApp, EvaluateHOL.listResult] using
          And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))

/-- Primitive conversions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_conversion {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (fromType toType : PrimType)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.fromTo fromType toType) [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.fromTo fromType toType) [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  have bodySimCopy := bodySim
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_conversion nextGenv compMap trace sourceEnv flatEnv source flat body fromType toType nextInvariant.1 bodySimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source nextSource sourceEnv body sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) (.fromTo fromType toType) [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app (.fromTo fromType toType) [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨lit, rfl⟩ := conversion_operand nextSource fromType toType operand successful
        have flatEq := (valueRel_literal_iff nextGenv lit flatOperand).mp valueRel
        subst flatOperand
        have primitive := conversion_related nextGenv nextInvariant.1 nextSource nextFlat fromType toType lit
        cases sourceApp : doApp (nextSource.refs, nextSource.ffi) (.fromTo fromType toType) [.litv lit] with
        | none => exact (successful sourceApp).elim
        | some sourceOut =>
          cases sourceOut with
          | mk store sourceResult =>
            cases store with
            | mk refs ffi =>
              cases flatApp : FlatSem.doAppNumeric nextFlat (.fromTo fromType toType) [.litv lit] with
              | none => simp [sourceApp, flatApp] at primitive
              | some flatOut =>
                cases flatOut with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | mk flatAfter flatResult =>
                    simp only [sourceApp, flatApp] at primitive
                    obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
                    refine ⟨nextGenv, exprSim_conversion nextGenv compMap trace sourceEnv flatEnv source flat body
                      fromType toType nextInvariant.1 bodySimCopy safe, ?_⟩
                    rw [EvaluateHOL.evaluate]
                    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
                    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
                    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                    rw [FlatSem.evaluate]
                    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
                    rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
                      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, getOpClass, astOpToFlatOp,
                      sourceApp, FlatSem.applyResult, FlatSem.doApp, flatApp]
                    cases resultRel with
                    | value valueRel =>
                      simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                        (And.intro nextGeneration forward))
                    | raise valueRel =>
                      simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                        (And.intro nextGeneration forward))
                    | abort error => simp [EvaluateHOL.listResult]

/-- Unary floating-point operations compose a bounded operand simulation. -/
theorem localEnvBounded_floatUnary {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (action : Arith)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action .float64T) [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.arith action .float64T) [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  have bodySimCopy := bodySim
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_floatUnary nextGenv compMap trace sourceEnv flatEnv source flat body action bodySimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source nextSource sourceEnv body sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) (.arith action .float64T) [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app (.arith action .float64T) [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨bits, rfl⟩ := floatUnary_operand nextSource action operand successful
        have flatEq := (valueRel_literal_iff nextGenv (.float64 bits) flatOperand).mp valueRel
        subst flatOperand
        have primitive := floatUnary_related nextGenv nextSource nextFlat action bits
        cases sourceApp : doApp (nextSource.refs, nextSource.ffi) (.arith action .float64T) [.litv (.float64 bits)] with
        | none => exact (successful sourceApp).elim
        | some sourceOut =>
          cases sourceOut with
          | mk store sourceResult =>
            cases store with
            | mk refs ffi =>
              cases flatApp : FlatSem.doAppNumeric nextFlat (.arith action .float64T) [.litv (.float64 bits)] with
              | none => simp [sourceApp, flatApp] at primitive
              | some flatOut =>
                cases flatOut with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | mk flatAfter flatResult =>
                    simp only [sourceApp, flatApp] at primitive
                    obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
                    refine ⟨nextGenv, exprSim_floatUnary nextGenv compMap trace sourceEnv flatEnv source flat body
                      action bodySimCopy safe, ?_⟩
                    rw [EvaluateHOL.evaluate]
                    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
                    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
                    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                    rw [FlatSem.evaluate]
                    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
                    rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
                      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, getOpClass, astOpToFlatOp,
                      sourceApp, FlatSem.applyResult, FlatSem.doApp, flatApp]
                    cases resultRel with
                    | value valueRel =>
                      simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                        (And.intro nextGeneration forward))
                    | raise valueRel =>
                      simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                        (And.intro nextGeneration forward))
                    | abort error => simp [EvaluateHOL.listResult]

/-- Boolean negation composes a bounded operand simulation. -/
theorem localEnvBounded_booleanNot {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith .not .boolT) [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.arith .not .boolT) [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  have bodySimCopy := bodySim
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_booleanNot nextGenv compMap trace sourceEnv flatEnv source flat body nextInvariant.1 bodySimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source nextSource sourceEnv body sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) (.arith .not .boolT) [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app (.arith .not .boolT) [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨b, rfl⟩ := booleanNot_operand nextSource operand successful
        have flatEq := (boolValueRel_iff nextGenv nextInvariant.1 b flatOperand).mp valueRel
        subst flatOperand
        obtain ⟨sourceApp, flatApp, _⟩ := booleanNot_related nextGenv nextInvariant.1 nextSource nextFlat b
        refine ⟨nextGenv, exprSim_booleanNot nextGenv compMap trace sourceEnv flatEnv source flat body
          nextInvariant.1 bodySimCopy safe, ?_⟩
        rw [EvaluateHOL.evaluate]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
        simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
        rw [FlatSem.evaluate]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
          (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        simpa [getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
          flatApp, EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
            (And.intro nextGeneration forward))

/-- Reference dereferences compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_opderef {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .opderef [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .opderef [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  have bodySimCopy := bodySim
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, exprSim_opderef nextGenv compMap trace sourceEnv flatEnv source flat body bodySimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source nextSource sourceEnv body sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) .opderef [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .opderef [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨flag, address, value, rfl, sourceLookup⟩ := opDeref_success nextSource operand successful
        have flatLocation := (valueRel_location_iff nextGenv flag address flatOperand).mp valueRel
        subst flatOperand
        obtain ⟨flatValue, flatLookup, resultRel⟩ :=
          stateRel_ref_lookup nextGenv nextSource nextFlat states address value sourceLookup
        refine ⟨nextGenv, exprSim_opderef nextGenv compMap trace sourceEnv flatEnv source flat body bodySimCopy safe, ?_⟩
        rw [EvaluateHOL.evaluate]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
        simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
        rw [FlatSem.evaluate]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
          (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, sourceLookup, astOpToFlatOp,
          FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, flatLookup, EvaluateHOL.listResult] using
          And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))

/-- Reference allocation compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_opref {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .opref [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .opref [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  have bodySimCopy := bodySim
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, exprSim_opref nextGenv compMap trace sourceEnv flatEnv source flat body bodySimCopy, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull source nextSource sourceEnv body sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatValue
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        obtain ⟨sourceApp, flatApp, locationRel, stateRel, reserved⟩ :=
          opref_related nextGenv nextSource nextFlat states value flatValue valueRel
        have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
          nextSource nextFlat (storeAlloc (.refv value) nextSource.refs).1
          (storeAlloc (.refv flatValue) nextFlat.refs).1 nextInvariant stateRel reserved
        refine ⟨nextGenv, exprSim_opref nextGenv compMap trace sourceEnv flatEnv source flat body bodySimCopy, ?_⟩
        rw [EvaluateHOL.evaluate]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
        simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
        rw [FlatSem.evaluate]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
          (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        simpa [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
          FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult] using
          And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))

/-- Compose reference assignment operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_opassign {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .opassign [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .opassign [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_opassign nextGenv compMap trace sourceEnv flatEnv source flat left right
      argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceValue, sourcePointer, rfl⟩ := two
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons pointerRel tail =>
        cases tail with
        | nil =>
          rename_i flatValue flatPointer
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) .opassign [sourcePointer, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .opassign [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨flag, address, refs, rfl, assigned⟩ := opAssign_success nextSource sourcePointer sourceValue successful
          have flatLocation := (valueRel_location_iff nextGenv flag address flatPointer).mp pointerRel
          subst flatPointer
          obtain ⟨flatRefs, sourceApp, flatApp, unitRel, stateRel, reserved⟩ :=
            opassign_related nextGenv nextSource nextFlat states flag address sourceValue flatValue valueRel refs assigned
          have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
            nextSource nextFlat refs flatRefs nextInvariant stateRel reserved
          refine ⟨nextGenv, exprSim_opassign nextGenv compMap trace sourceEnv flatEnv source flat left right argsSimCopy safe, ?_⟩
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
          rw [FlatSem.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
          rw [(FlatSem.fixClock_evaluations flatEnv flat
            [compileExp trace compMap right, compileExp trace compMap left]
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simpa [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult] using
            And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))


end Flapjack.Compiler.Backend.SourceToFlat
