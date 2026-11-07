import Flapjack.Compiler.Backend.BviTailrec.Proofs.Semantics

/-! Cases of the tail-recursion scan type-soundness invariant. The BVI
evaluator is not yet source-reviewed, so these supporting results are untagged. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi BvlSem

/-- Successful evaluation agrees with the contexts and result types inferred
by a source-shaped list scan. -/
def scanSound {C F : Type} (ctx : List ValueType) (loc : Nat) (xs : List Bvi.Exp) : Prop :=
  ∀ (env : List Value) (state next : BviSem.BviState C F) (values : List Value),
    tyRel env ctx → BviSem.evaluate xs env state = (.val values, next) →
      (∀ entry ∈ scanExpr ctx loc xs, tyRel env entry.1) ∧
        tyRel values ((scanExpr ctx loc xs).map fun (_, ty, _, _) => ty)

/-- Joining type facts cannot invalidate a value that satisfies the left
branch's type. -/
theorem valueMatchesType_decide_left (value : Value) (left right : ValueType)
    (typed : valueMatchesType value left) : valueMatchesType value (decideType left right) := by
  cases left <;> cases right <;> simp_all [valueMatchesType, decideType]

/-- Joining type facts cannot invalidate a value that satisfies the right
branch's type. -/
theorem valueMatchesType_decide_right (value : Value) (left right : ValueType)
    (typed : valueMatchesType value right) : valueMatchesType value (decideType left right) := by
  cases left <;> cases right <;> simp_all [valueMatchesType, decideType]

/-- The type selected for a conditional is sound for a value from either
branch, including the extra accumulator-type join. -/
theorem valueMatchesType_ifJoin (value : Value) (left right : ValueType) (op : Option AssocOp)
    (typed : valueMatchesType value left ∨ valueMatchesType value right) :
    valueMatchesType value (match op with
      | none => decideType left right
      | some a => decideType left (decideType right (opType a))) := by
  cases op with
  | none =>
    rcases typed with h | h
    · exact valueMatchesType_decide_left value left right h
    · exact valueMatchesType_decide_right value left right h
  | some a =>
    rcases typed with h | h
    · exact valueMatchesType_decide_left value left _ h
    · exact valueMatchesType_decide_right value left _ (valueMatchesType_decide_left value right _ h)

/-- The empty scan is sound for successful evaluation. -/
theorem scanSound_nil {C F : Type} (ctx : List ValueType) (loc : Nat) :
    scanSound (C := C) (F := F) ctx loc [] := by
  intro env state next values related run
  simp [BviSem.evaluate] at run
  obtain ⟨rfl, _⟩ := run
  simp [scanExpr.eq_def, tyRel]

/-- The variable case of scan soundness. -/
theorem scanSound_var {C F : Type} (ctx : List ValueType) (loc n : Nat) :
    scanSound (C := C) (F := F) ctx loc [.var n] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.var n) env state next values run
  exact scanExpr_var_sound ctx loc n env state next value related run

/-- A successfully decoded list is a block, so it is not a thunk pointer. -/
theorem listValue_notThunk (value : Value) (refs : HolFiniteMapExact Nat (Ref Value))
    (xs : List Value) (decoded : valueToList value = some xs) :
    BviSem.destThunk value refs = .notThunk := by
  cases value with
  | block tag fields => rfl
  | _ => simp [valueToList] at decoded

/-- A successful force cannot read a value described by an integer or list
context entry, because those values are not thunk pointers. -/
theorem force_context_any {C F : Type} (ctx : List ValueType) (loc n : Nat)
    (env : List Value) (state next : BviSem.BviState C F) (value : Value)
    (related : tyRel env ctx)
    (run : BviSem.evaluate [.force loc n] env state = (.val [value], next)) :
    ctx[n]?.getD .any = .any := by
  cases lookup : env[n]? with
  | none => simp [BviSem.evaluate, lookup] at run
  | some thunk =>
    have isThunk : BviSem.destThunk thunk state.refs ≠ .notThunk := by
      intro notThunk
      simp [BviSem.evaluate, lookup, notThunk] at run
    obtain ⟨ty, found, typed⟩ := tyRel_lookup_value related n thunk lookup
    cases ty with
    | int =>
      obtain ⟨integer, rfl⟩ := typed.1 rfl
      exact False.elim (isThunk rfl)
    | list =>
      obtain ⟨xs, decoded⟩ := typed.2 rfl
      exact False.elim (isThunk (listValue_notThunk thunk state.refs xs decoded))
    | any => simp [found]

/-- The force case of the source scan type-soundness invariant. -/
theorem scanSound_force {C F : Type} (ctx : List ValueType) (loc place index : Nat) :
    scanSound (C := C) (F := F) ctx loc [.force place index] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.force place index) env state next values run
  have any := force_context_any ctx place index env state next value related run
  rw [scanExpr_single, scanSing.eq_def]
  simp only [any, List.mem_singleton, forall_eq, List.map_cons, List.map_nil]
  exact ⟨related, by simp [tyRel]⟩

/-- Small constants produce integer values and preserve scan soundness. The
side condition is derived from successful BVI evaluation. -/
theorem scanSound_intConst {C F : Type} (ctx : List ValueType) (loc : Nat) (k : Int) :
    scanSound (C := C) (F := F) ctx loc [.op (.intOp (.const k)) []] := by
  intro env state next values related run
  have small : BackendCommon.smallEnoughInt k := by
    by_contra notSmall
    simp [BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, notSmall] at run
  have same : ((.val values : BviSem.BviResult), next) = (.val [.number k], state) := by
    exact run.symm.trans (evaluate_smallInt k small env state)
  cases same
  have smallBool : (decide (-268435457 ≤ k) && decide (k ≤ 268435457)) = true := by
    simpa [BackendCommon.smallEnoughInt] using small
  have constOk : isConst (.intOp (.const k)) = true := by
    change (decide (-268435457 ≤ k) && decide (k ≤ 268435457)) = true
    exact smallBool
  have arg : argType (.intOp (.const k)) = .int := by
    change (if (decide (-268435457 ≤ k) && decide (k ≤ 268435457)) then ValueType.int else ValueType.any) = ValueType.int
    simp [smallBool]
  rw [scanExpr_single, scanSing.eq_def]
  simp [fromOp, arg, constOk, BEq.beq, instBEqAssocOp.beq, instBEqValueType.beq,
    AssocOp.ctorIdx, ValueType.ctorIdx, tyRel]
  exact related

/-- The empty-list constructor produces a value matching the list type
inferred by the scan. -/
theorem scanSound_listNil {C F : Type} (ctx : List ValueType) (loc : Nat) :
    scanSound (C := C) (F := F) ctx loc [.op (.blockOp (.cons 0)) []] := by
  intro env state next values related run
  have same : ((.val values : BviSem.BviResult), next) = (.val [listToValue []], state) :=
    run.symm.trans (evaluate_nil env state)
  cases same
  rw [scanExpr_single, scanSing.eq_def]
  simp [fromOp, argType, BEq.beq, instBEqAssocOp.beq, instBEqValueType.beq,
    AssocOp.ctorIdx, ValueType.ctorIdx, tyRel, valueToList_listToValue]
  exact related

/-- A singleton scan that leaves the context unchanged and infers `any` is
sound for any successful BVI evaluation of that expression. -/
theorem scanSound_default {C F : Type} (ctx : List ValueType) (loc : Nat) (e : Bvi.Exp)
    (scan : scanSing ctx loc e = (ctx, .any, false, none)) :
    scanSound (C := C) (F := F) ctx loc [e] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton e env state next values run
  rw [scanExpr_single, scan]
  simp only [List.mem_singleton, forall_eq, List.map_cons, List.map_nil]
  exact ⟨related, by simp [tyRel]⟩

/-- Operators outside the accumulator and integer classes use the default
scan result, apart from the explicitly recognized nil constructor. -/
theorem scanSound_op_other {C F : Type} (ctx : List ValueType) (loc : Nat)
    (op : ClosLang.Op) (xs : List Bvi.Exp) (notAccumulator : fromOp op = .noop)
    (notInteger : argType op ≠ .int) :
    scanSound (C := C) (F := F) ctx loc [.op op xs] := by
  by_cases nilCase : op = .blockOp (.cons 0) ∧ xs = []
  · obtain ⟨rfl, rfl⟩ := nilCase
    exact scanSound_listNil ctx loc
  · apply scanSound_default
    rw [scanSing.eq_def]
    dsimp only
    rw [notAccumulator]
    have otherType : (argType op == .int) = false := by
      cases h : argType op <;> simp_all [BEq.beq, instBEqValueType.beq, ValueType.ctorIdx]
    simp only [show (AssocOp.noop == AssocOp.noop) = true from rfl,
      otherType, Bool.false_eq_true, ↓reduceIte]
    split
    · exact False.elim (nilCase ⟨rfl, rfl⟩)
    · rfl

/-- Successful primitive evaluation consists of successful argument
evaluation followed by successful primitive dispatch. -/
theorem evaluateOp_success {C F : Type} (op : ClosLang.Op) (args : List Bvi.Exp) (env : List Value)
    (state next : BviSem.BviState C F) (value : Value)
    (run : BviSem.evaluate [.op op args] env state = (.val [value], next)) :
    ∃ argValues middle, BviSem.evaluate args env state = (.val argValues, middle) ∧
      BviSem.doApp op argValues.reverse middle = .val (value, next) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate] at run
  cases hargs : BviSem.evaluate args env state with
  | mk result middle =>
    cases result with
    | err error => simp [hargs] at run
    | val argValues =>
      cases hdispatch : BviSem.doApp op argValues.reverse middle with
      | err error => simp [hargs, hdispatch] at run
      | val output =>
        obtain ⟨returned, last⟩ := output
        have same : returned = value ∧ last = next := by
          simpa [hargs, hdispatch] using run
        obtain ⟨rfl, rfl⟩ := same
        exact ⟨argValues, middle, rfl, hdispatch⟩

/-- A successful integer arithmetic primitive has integer operands and an
integer result. -/
theorem doApp_arith_success {C F : Type} (op : ClosLang.IntOp) (x y result : Value)
    (state next : BviSem.BviState C F) (allowed : isArith (.intOp op) = true)
    (run : BviSem.doApp (.intOp op) [x, y] state = .val (result, next)) :
    (∃ a, x = .number a) ∧ (∃ b, y = .number b) ∧ (∃ c, result = .number c) := by
  cases op <;> try simp [isArith] at allowed <;>
    cases x <;> cases y <;>
    simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp, BviSem.fromBvl_toBvl]
  all_goals
    obtain ⟨same, _⟩ := run
    subst result
    exact ⟨_, rfl⟩

/-- A successful binary integer primitive whose operands are classified as
integers has integer operands. -/
theorem doApp_integer_operands {C F : Type} (op : ClosLang.IntOp) (x y result : Value)
    (state next : BviSem.BviState C F) (allowed : argType (.intOp op) = .int)
    (run : BviSem.doApp (.intOp op) [x, y] state = .val (result, next)) :
    (∃ a, x = .number a) ∧ (∃ b, y = .number b) := by
  cases op <;> cases x <;> cases y <;>
    simp_all [argType, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp, BviSem.fromBvl_toBvl]

/-- Successful dispatch of a non-constant integer-argument primitive
requires two operands. -/
theorem doApp_integer_length {C F : Type} (op : ClosLang.IntOp) (args : List Value) (result : Value)
    (state next : BviSem.BviState C F) (integerArgs : argType (.intOp op) = .int)
    (notConst : ∀ k, op ≠ .const k)
    (run : BviSem.doApp (.intOp op) args state = .val (result, next)) : args.length = 2 := by
  cases op <;> try simp [argType] at integerArgs
  case const k => exact (notConst k rfl).elim
  all_goals
    cases args with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyNumeric, BvlSem.doIntApp] at run
    | cons a rest =>
      cases rest with
      | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BvlSem.applyNumeric, BvlSem.doIntApp] at run
      | cons b rest =>
        cases rest with
        | nil => rfl
        | cons c rest =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
            BvlSem.applyNumeric, BvlSem.doIntApp] at run

/-- Successful list append implies that both operands and the result decode
as source lists. -/
theorem doApp_append_success {C F : Type} (x y result : Value)
    (state next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp .listAppend) [x, y] state = .val (result, next)) :
    (∃ xs, valueToList x = some xs) ∧ (∃ ys, valueToList y = some ys) ∧
      (∃ zs, valueToList result = some zs) := by
  cases hx : valueToList x with
  | none =>
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyBlock, hx] at run
  | some xs =>
    cases hy : valueToList y with
    | none =>
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyBlock, hx, hy] at run
    | some ys =>
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyBlock, hx, hy, BviSem.fromBvl_toBvl] at run
      obtain ⟨rfl, _⟩ := run
      exact ⟨⟨xs, rfl⟩, ⟨ys, rfl⟩, ⟨xs ++ ys, valueToList_listToValue _⟩⟩

/-- Successful append dispatch requires exactly two arguments. -/
theorem doApp_append_length {C F : Type} (args : List Value) (result : Value)
    (state next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp .listAppend) args state = .val (result, next)) :
    args.length = 2 := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | cons b rest =>
      cases rest with
      | nil => rfl
      | cons c rest =>
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run

/-- Successful source list-append evaluation has exactly two operand
expressions. -/
theorem evaluate_append_length {C F : Type} (args : List Bvi.Exp) (env : List Value)
    (state next : BviSem.BviState C F) (value : Value)
    (run : BviSem.evaluate [.op (.blockOp .listAppend) args] env state = (.val [value], next)) :
    args.length = 2 := by
  obtain ⟨argValues, middle, argsRun, dispatch⟩ :=
    evaluateOp_success (.blockOp .listAppend) args env state next value run
  have length := doApp_append_length argValues.reverse value middle next dispatch
  have valuesLength := BviSem.evaluate_length args env state middle argValues argsRun
  simpa [valuesLength] using length

/-- Successful integer-constant dispatch requires no arguments. -/
theorem doApp_const_length {C F : Type} (k : Int) (args : List Value) (result : Value)
    (state next : BviSem.BviState C F)
    (run : BviSem.doApp (.intOp (.const k)) args state = .val (result, next)) : args = [] := by
  cases args with
  | nil => rfl
  | cons x xs =>
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run

/-- Integer constants are sound for every operand list; nonempty lists
cannot evaluate successfully. -/
theorem scanSound_intConst_all {C F : Type} (ctx : List ValueType) (loc : Nat)
    (k : Int) (args : List Bvi.Exp) :
    scanSound (C := C) (F := F) ctx loc [.op (.intOp (.const k)) args] := by
  cases args with
  | nil => exact scanSound_intConst ctx loc k
  | cons x xs =>
    intro env state next values related run
    obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.op (.intOp (.const k)) (x :: xs)) env state next values run
    obtain ⟨argValues, middle, argsRun, dispatch⟩ :=
      evaluateOp_success (.intOp (.const k)) (x :: xs) env state next value run
    have empty := doApp_const_length k argValues.reverse value middle next dispatch
    have count := BviSem.evaluate_length (x :: xs) env state middle argValues argsRun
    have emptyLength : argValues.length = 0 := by simpa using congrArg List.length empty
    simp [emptyLength] at count

/-- A successful two-expression evaluation exposes the two sequential
singleton evaluations. -/
theorem evaluatePair_success {C F : Type} (x y : Bvi.Exp) (env : List Value)
    (state next : BviSem.BviState C F) (values : List Value)
    (run : BviSem.evaluate [x, y] env state = (.val values, next)) :
    ∃ vx vy middle, values = [vx, vy] ∧
      BviSem.evaluate [x] env state = (.val [vx], middle) ∧
      BviSem.evaluate [y] env middle = (.val [vy], next) := by
  change BviSem.evaluateTuple ([x, y], env, state) = _ at run
  rw [BviSem.evaluateCons] at run
  cases hx : BviSem.evaluate [x] env state with
  | mk result middle =>
    cases result with
    | err error => simp [BviSem.evaluateTuple, hx] at run
    | val valuesX =>
      obtain ⟨vx, rfl⟩ := BviSem.evaluate_singleton x env state middle valuesX hx
      cases hy : BviSem.evaluate [y] env middle with
      | mk result last =>
        cases result with
        | err error => simp [BviSem.evaluateTuple, hx, hy] at run
        | val valuesY =>
          obtain ⟨vy, rfl⟩ := BviSem.evaluate_singleton y env middle last valuesY hy
          simp only [BviSem.evaluateTuple, hx, hy, Flapjack.holHd,
            Prod.mk.injEq, SemanticPrimitivesHOL.Result.val.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          exact ⟨vx, vy, middle, rfl, rfl, hy⟩

/-- An arithmetic scan either preserves the context or refines the two
operands as integers, and its result type is integer or unconstrained. -/
theorem scanSing_arith_shape (ctx : List ValueType) (loc : Nat) (op : ClosLang.IntOp)
    (x y : Bvi.Exp) (allowed : isArith (.intOp op) = true) :
    ((scanSing ctx loc (.op (.intOp op) [x, y])).1 = ctx ∨
      (scanSing ctx loc (.op (.intOp op) [x, y])).1 = updateContext .int ctx x y) ∧
    ((scanSing ctx loc (.op (.intOp op) [x, y])).2.1 = .int ∨
      (scanSing ctx loc (.op (.intOp op) [x, y])).2.1 = .any) := by
  cases op <;> try simp [isArith] at allowed
  all_goals
    rw [scanSing.eq_def]
    dsimp only
    simp [fromOp, argType, isConst, BEq.beq, instBEqAssocOp.beq,
      instBEqValueType.beq, AssocOp.ctorIdx, ValueType.ctorIdx, opType]
  case add =>
    by_cases h : (checkOp ctx .plus loc (.op (.intOp .add) [x, y])).isSome = true <;>
      by_cases ht : term ctx .int (.op (.intOp .add) [x, y]) = true <;> simp [h, ht]
  case mult =>
    by_cases h : (checkOp ctx .times loc (.op (.intOp .mult) [x, y])).isSome = true <;>
      by_cases ht : term ctx .int (.op (.intOp .mult) [x, y]) = true <;> simp [h, ht]

/-- Arithmetic operations preserve the scan type-soundness invariant. -/
theorem scanSound_arith {C F : Type} (ctx : List ValueType) (loc : Nat)
    (op : ClosLang.IntOp) (x y : Bvi.Exp) (allowed : isArith (.intOp op) = true) :
    scanSound (C := C) (F := F) ctx loc [.op (.intOp op) [x, y]] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.op (.intOp op) [x, y]) env state next values run
  obtain ⟨argValues, middle, argsRun, dispatch⟩ := evaluateOp_success (.intOp op) [x, y] env state next value run
  obtain ⟨vx, vy, between, rfl, xRun, yRun⟩ := evaluatePair_success x y env state middle argValues argsRun
  have dispatch' : BviSem.doApp (.intOp op) [vy, vx] middle = .val (value, next) := by
    simpa using dispatch
  obtain ⟨⟨b, rfl⟩, ⟨a, rfl⟩, ⟨c, rfl⟩⟩ := doApp_arith_success op vy vx value middle next allowed dispatch'
  have refined : tyRel env (updateContext .int ctx x y) :=
    tyRel_updateContext_of_evaluation related .int x y state between between middle
      (.number a) (.number b) xRun yRun (by simp [valueMatchesType]) (by simp [valueMatchesType])
  obtain ⟨contextShape, typeShape⟩ := scanSing_arith_shape ctx loc op x y allowed
  rw [scanExpr_single]
  simp only [List.mem_singleton, forall_eq, List.map_cons, List.map_nil]
  constructor
  · rcases contextShape with same | same <;> rw [same]
    · exact related
    · exact refined
  · apply List.Forall₂.cons
    · rcases typeShape with same | same <;> rw [same] <;> simp
    · exact .nil

/-- A binary integer-argument primitive outside the accumulator class has
an unconstrained result and can only refine its operand variables as integers. -/
theorem scanSing_otherInt_shape (ctx : List ValueType) (loc : Nat) (op : ClosLang.IntOp)
    (x y : Bvi.Exp) (notAccumulator : fromOp (.intOp op) = .noop)
    (integerArgs : argType (.intOp op) = .int) :
    ((scanSing ctx loc (.op (.intOp op) [x, y])).1 = ctx ∨
      (scanSing ctx loc (.op (.intOp op) [x, y])).1 = updateContext .int ctx x y) ∧
    (scanSing ctx loc (.op (.intOp op) [x, y])).2.1 = .any := by
  rw [scanSing.eq_def]
  dsimp only
  simp [notAccumulator, integerArgs, BEq.beq, instBEqAssocOp.beq,
    instBEqValueType.beq, AssocOp.ctorIdx, ValueType.ctorIdx]
  by_cases h : isConst (.intOp op) = true <;> simp [h]

/-- Binary integer primitives outside the accumulator class preserve scan
type soundness when their dispatch succeeds. -/
theorem scanSound_otherInt {C F : Type} (ctx : List ValueType) (loc : Nat)
    (op : ClosLang.IntOp) (x y : Bvi.Exp) (notAccumulator : fromOp (.intOp op) = .noop)
    (integerArgs : argType (.intOp op) = .int) :
    scanSound (C := C) (F := F) ctx loc [.op (.intOp op) [x, y]] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.op (.intOp op) [x, y]) env state next values run
  obtain ⟨argValues, middle, argsRun, dispatch⟩ := evaluateOp_success (.intOp op) [x, y] env state next value run
  obtain ⟨vx, vy, between, rfl, xRun, yRun⟩ := evaluatePair_success x y env state middle argValues argsRun
  have dispatch' : BviSem.doApp (.intOp op) [vy, vx] middle = .val (value, next) := by simpa using dispatch
  obtain ⟨⟨b, rfl⟩, ⟨a, rfl⟩⟩ := doApp_integer_operands op vy vx value middle next integerArgs dispatch'
  have refined : tyRel env (updateContext .int ctx x y) :=
    tyRel_updateContext_of_evaluation related .int x y state between between middle
      (.number a) (.number b) xRun yRun (by simp [valueMatchesType]) (by simp [valueMatchesType])
  obtain ⟨contextShape, typeShape⟩ := scanSing_otherInt_shape ctx loc op x y notAccumulator integerArgs
  rw [scanExpr_single]
  simp only [List.mem_singleton, forall_eq, List.map_cons, List.map_nil]
  constructor
  · rcases contextShape with same | same <;> rw [same]
    · exact related
    · exact refined
  · apply List.Forall₂.cons
    · rw [typeShape]; simp
    · exact .nil

/-- A successful non-constant integer primitive with integer arguments has
two source operands. -/
theorem evaluate_integer_length {C F : Type} (op : ClosLang.IntOp) (args : List Bvi.Exp)
    (env : List Value) (state next : BviSem.BviState C F) (value : Value)
    (integerArgs : argType (.intOp op) = .int) (notConst : ∀ k, op ≠ .const k)
    (run : BviSem.evaluate [.op (.intOp op) args] env state = (.val [value], next)) :
    args.length = 2 := by
  obtain ⟨argValues, middle, argsRun, dispatch⟩ := evaluateOp_success (.intOp op) args env state next value run
  have length := doApp_integer_length op argValues.reverse value middle next integerArgs notConst dispatch
  have valuesLength := BviSem.evaluate_length args env state middle argValues argsRun
  simpa [valuesLength] using length

/-- Non-constant integer operations preserve scan soundness for every arity. -/
theorem scanSound_intNonconst {C F : Type} (ctx : List ValueType) (loc : Nat)
    (op : ClosLang.IntOp) (args : List Bvi.Exp) (notConst : ∀ k, op ≠ .const k) :
    scanSound (C := C) (F := F) ctx loc [.op (.intOp op) args] := by
  by_cases integerArgs : argType (.intOp op) = .int
  · intro env state next values related run
    obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.op (.intOp op) args) env state next values run
    have length := evaluate_integer_length op args env state next value integerArgs notConst run
    cases args with
    | nil => simp at length
    | cons x xs =>
      cases xs with
      | nil => simp at length
      | cons y ys =>
        cases ys with
        | cons z zs => simp at length
        | nil =>
          by_cases arith : isArith (.intOp op) = true
          · exact scanSound_arith ctx loc op x y arith env state next [value] related run
          · have notAccumulator : fromOp (.intOp op) = .noop := by
              cases op <;> simp_all [isArith, fromOp]
            exact scanSound_otherInt ctx loc op x y notAccumulator integerArgs env state next [value] related run
  · have notAccumulator : fromOp (.intOp op) = .noop := by
      cases op <;> simp_all [argType, fromOp]
    exact scanSound_op_other ctx loc (.intOp op) args notAccumulator integerArgs

/-- Every integer primitive preserves scan type soundness, including arity
errors and out-of-range constants. -/
theorem scanSound_intOp {C F : Type} (ctx : List ValueType) (loc : Nat)
    (op : ClosLang.IntOp) (args : List Bvi.Exp) :
    scanSound (C := C) (F := F) ctx loc [.op (.intOp op) args] := by
  cases op with
  | const k => exact scanSound_intConst_all ctx loc k args
  | _ => apply scanSound_intNonconst; intro k; simp

/-- A two-operand list-append scan can only preserve the context or refine
both operands as lists, and its result type is list or unconstrained. -/
theorem scanSing_append_shape (ctx : List ValueType) (loc : Nat) (x y : Bvi.Exp) :
    ((scanSing ctx loc (.op (.blockOp .listAppend) [x, y])).1 = ctx ∨
      (scanSing ctx loc (.op (.blockOp .listAppend) [x, y])).1 = updateContext .list ctx x y) ∧
    ((scanSing ctx loc (.op (.blockOp .listAppend) [x, y])).2.1 = .list ∨
      (scanSing ctx loc (.op (.blockOp .listAppend) [x, y])).2.1 = .any) := by
  rw [scanSing.eq_def]
  dsimp only
  simp [fromOp, BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx, opType]
  by_cases h : (checkOp ctx .append loc (.op (.blockOp .listAppend) [x, y])).isSome = true <;>
    by_cases ht : term ctx .list (.op (.blockOp .listAppend) [x, y]) = true <;> simp [h, ht]

/-- A successful two-operand list append preserves the scan type-soundness
invariant. -/
theorem scanSound_append {C F : Type} (ctx : List ValueType) (loc : Nat) (x y : Bvi.Exp) :
    scanSound (C := C) (F := F) ctx loc [.op (.blockOp .listAppend) [x, y]] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.op (.blockOp .listAppend) [x, y]) env state next values run
  obtain ⟨argValues, middle, argsRun, dispatch⟩ :=
    evaluateOp_success (.blockOp .listAppend) [x, y] env state next value run
  obtain ⟨vx, vy, between, rfl, xRun, yRun⟩ := evaluatePair_success x y env state middle argValues argsRun
  have dispatch' : BviSem.doApp (.blockOp .listAppend) [vy, vx] middle = .val (value, next) := by
    simpa using dispatch
  obtain ⟨⟨ys, dy⟩, ⟨xs, dx⟩, ⟨zs, dz⟩⟩ := doApp_append_success vy vx value middle next dispatch'
  have typedX : valueMatchesType vx .list := by simp [valueMatchesType, dx]
  have typedY : valueMatchesType vy .list := by simp [valueMatchesType, dy]
  have refined : tyRel env (updateContext .list ctx x y) :=
    tyRel_updateContext_of_evaluation related .list x y state between between middle vx vy xRun yRun typedX typedY
  obtain ⟨contextShape, typeShape⟩ := scanSing_append_shape ctx loc x y
  rw [scanExpr_single]
  simp only [List.mem_singleton, forall_eq, List.map_cons, List.map_nil]
  constructor
  · rcases contextShape with same | same <;> rw [same]
    · exact related
    · exact refined
  · apply List.Forall₂.cons
    · rcases typeShape with same | same <;> rw [same] <;> simp [dz]
    · exact .nil

/-- The source append scan is sound for every operand list, including
wrong-arity lists which cannot evaluate successfully. -/
theorem scanSound_append_all {C F : Type} (ctx : List ValueType) (loc : Nat) (args : List Bvi.Exp) :
    scanSound (C := C) (F := F) ctx loc [.op (.blockOp .listAppend) args] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.op (.blockOp .listAppend) args) env state next values run
  have length := evaluate_append_length args env state next value run
  cases args with
  | nil => simp at length
  | cons x xs =>
    cases xs with
    | nil => simp at length
    | cons y ys =>
      cases ys with
      | nil => exact scanSound_append ctx loc x y env state next [value] related run
      | cons z zs => simp at length

/-- Every primitive-operation scan preserves the source type-soundness
invariant for successful BVI evaluation. -/
theorem scanSound_op {C F : Type} (ctx : List ValueType) (loc : Nat)
    (op : ClosLang.Op) (args : List Bvi.Exp) :
    scanSound (C := C) (F := F) ctx loc [.op op args] := by
  cases op with
  | intOp operation => exact scanSound_intOp ctx loc operation args
  | blockOp operation =>
    cases operation with
    | listAppend => exact scanSound_append_all ctx loc args
    | _ => apply scanSound_op_other <;> simp [fromOp, argType]
  | _ => apply scanSound_op_other <;> simp [fromOp, argType]

/-- Expressions whose scan has the source default result satisfy the scan
invariant whenever they evaluate successfully. -/
theorem scanSound_default_cases {C F : Type} (ctx : List ValueType) (loc : Nat) :
    (∀ e, scanSound (C := C) (F := F) ctx loc [.raise e]) ∧
    (∀ xs, scanSound (C := C) (F := F) ctx loc [.return xs]) ∧
    (∀ ticks dest args handler, scanSound (C := C) (F := F) ctx loc [.call ticks dest args handler]) ∧
    (∀ rets ticks dest args body, scanSound (C := C) (F := F) ctx loc [.letCall rets ticks dest args body]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> apply scanSound_default <;> rw [scanSing.eq_def]

/-- The tick case follows from soundness of the expression it evaluates. -/
theorem scanSound_tick {C F : Type} (ctx : List ValueType) (loc : Nat) (body : Bvi.Exp)
    (bodyIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [body]) :
    scanSound (C := C) (F := F) ctx loc [.tick body] := by
  intro env state next values related run
  by_cases clock : state.clock = 0
  · simp [BviSem.evaluate, clock] at run
  ·
    have bodyRun : BviSem.evaluate [body] env (BviSem.decClock 1 state) = (.val values, next) := by
      simpa [BviSem.evaluate, clock] using run
    have sound := bodyIH ctx env (BviSem.decClock 1 state) next values related bodyRun
    rw [scanExpr_single, scanSing.eq_def]
    simpa only [scanExpr_single] using sound

/-- Successful conditional evaluation first evaluates the condition and then
exactly one branch. -/
theorem evaluateIf_success {C F : Type} (condition yes no : Bvi.Exp) (env : List Value)
    (state next : BviSem.BviState C F) (values : List Value)
    (run : BviSem.evaluate [.ifThenElse condition yes no] env state = (.val values, next)) :
    ∃ value middle, BviSem.evaluate [condition] env state = (.val [value], middle) ∧
      ((asBool value = some true ∧ BviSem.evaluate [yes] env middle = (.val values, next)) ∨
       (asBool value = some false ∧ BviSem.evaluate [no] env middle = (.val values, next))) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate] at run
  cases hcond : BviSem.evaluate [condition] env state with
  | mk result middle =>
    cases result with
    | err error => simp [hcond] at run
    | val vs =>
      obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton condition env state middle vs hcond
      simp only [hcond] at run
      change (match asBool value with
        | none => (.err (.abort .typeError), middle)
        | some true => BviSem.evaluate [yes] env middle
        | some false => BviSem.evaluate [no] env middle) = (.val values, next) at run
      cases test : asBool value with
      | none => simp [test] at run
      | some choice =>
        cases choice with
        | false =>
          refine ⟨value, middle, rfl, Or.inr ⟨test, ?_⟩⟩
          simpa [test] using run
        | true =>
          refine ⟨value, middle, rfl, Or.inl ⟨test, ?_⟩⟩
          simpa [test] using run

/-- The conditional scan is sound when the condition and both branches
satisfy the source induction hypotheses. -/
theorem scanSound_if {C F : Type} (ctx : List ValueType) (loc : Nat) (condition yes no : Bvi.Exp)
    (condIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [condition])
    (yesIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [yes])
    (noIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [no]) :
    scanSound (C := C) (F := F) ctx loc [.ifThenElse condition yes no] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.ifThenElse condition yes no) env state next values run
  obtain ⟨condValue, middle, condRun, branch⟩ := evaluateIf_success condition yes no env state next [value] run
  have condSound := condIH ctx env state middle [condValue] related condRun
  simp only [scanExpr_single, List.mem_singleton, forall_eq, List.map_cons, List.map_nil] at condSound
  let ci := (scanSing ctx loc condition).1
  let y := scanSing ci loc yes
  let n := scanSing ci loc no
  have branchSound : (tyRel env y.1 ∧ valueMatchesType value y.2.1) ∨
      (tyRel env n.1 ∧ valueMatchesType value n.2.1) := by
    rcases branch with ⟨_, yesRun⟩ | ⟨_, noRun⟩
    · have sound := yesIH ci env middle next [value] condSound.1 yesRun
      simp only [scanExpr_single, List.mem_singleton, forall_eq, List.map_cons, List.map_nil] at sound
      left
      exact ⟨sound.1, by simpa [tyRel, valueMatchesType] using sound.2⟩
    · have sound := noIH ci env middle next [value] condSound.1 noRun
      simp only [scanExpr_single, List.mem_singleton, forall_eq, List.map_cons, List.map_nil] at sound
      right
      exact ⟨sound.1, by simpa [tyRel, valueMatchesType] using sound.2⟩
  have sameLength : y.1.length = n.1.length :=
    (scanSing_context_length ci loc yes).trans (scanSing_context_length ci loc no).symm
  have merged := tyRel_decideType y.1 n.1 env ⟨branchSound.imp And.left And.left, sameLength⟩
  have typed := valueMatchesType_ifJoin value y.2.1 n.2.1 (y.2.2.2.orElse fun _ => n.2.2.2)
    (branchSound.imp And.right And.right)
  rw [scanExpr_single, scanSing.eq_def]
  dsimp only
  simp only [List.mem_singleton, forall_eq, List.map_cons, List.map_nil]
  exact ⟨merged, .cons typed .nil⟩

/-- Successful local-binding evaluation first evaluates the binding list and
then the body in the extended environment. -/
theorem evaluateLet_success {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp) (env : List Value)
    (state next : BviSem.BviState C F) (values : List Value)
    (run : BviSem.evaluate [.let bindings body] env state = (.val values, next)) :
    ∃ bound middle, BviSem.evaluate bindings env state = (.val bound, middle) ∧
      BviSem.evaluate [body] (bound ++ env) middle = (.val values, next) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate] at run
  cases hbind : BviSem.evaluate bindings env state with
  | mk result middle =>
    cases result with
    | err error => simp [hbind] at run
    | val bound =>
      refine ⟨bound, middle, rfl, ?_⟩
      simpa [hbind] using run

/-- Removing the bound-value prefix from a related extended context leaves
the outer environment and its corresponding context related. -/
theorem tyRel_drop_prefix (bound env : List Value) (types : List ValueType)
    (h : tyRel (bound ++ env) types) : tyRel env (types.drop bound.length) := by
  have dropped := List.forall₂_drop bound.length h
  simpa only [tyRel, List.drop_append_length] using dropped

/-- The local-binding scan is sound when the bindings and body satisfy their
source induction hypotheses. -/
theorem scanSound_let {C F : Type} (ctx : List ValueType) (loc : Nat)
    (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (bindingsIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc bindings)
    (bodyIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [body]) :
    scanSound (C := C) (F := F) ctx loc [.let bindings body] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.let bindings body) env state next values run
  obtain ⟨bound, middle, bindRun, bodyRun⟩ := evaluateLet_success bindings body env state next [value] run
  have bindSound := bindingsIH ctx env state middle bound related bindRun
  rw [scanExpr_list] at bindSound
  let scans := scanList ctx loc bindings
  let types := scans.map fun (_, ty, _, _) => ty
  let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
  have lastSound : tyRel env last := by
    cases hlast : scans.getLast? with
    | none => simpa [last, hlast] using related
    | some entry =>
      have sound := bindSound.1 entry (List.mem_of_getLast? hlast)
      obtain ⟨a, b, c, d⟩ := entry
      simpa [last, hlast] using sound
  have extended : tyRel (bound ++ env) (types ++ last) :=
    tyRel_append env last types bound ⟨lastSound, bindSound.2⟩
  have bodySound := bodyIH (types ++ last) (bound ++ env) middle next [value] extended bodyRun
  simp only [scanExpr_single, List.mem_singleton, forall_eq, List.map_cons, List.map_nil] at bodySound
  have dropped := tyRel_drop_prefix bound env (scanSing (types ++ last) loc body).1 bodySound.1
  have boundLength : bound.length = scans.length := by
    rw [BviSem.evaluate_length bindings env state middle bound bindRun]
    exact (scanList_length ctx loc bindings).symm
  rw [boundLength] at dropped
  rw [scanExpr_single, scanSing.eq_def]
  dsimp only
  simp only [List.mem_singleton, forall_eq, List.map_cons, List.map_nil]
  exact ⟨dropped, bodySound.2⟩

/-- Sequential evaluation and context threading preserve scan soundness,
assuming the corresponding induction hypotheses for head and tail. -/
theorem scanSound_cons {C F : Type} (ctx : List ValueType) (loc : Nat) (x : Bvi.Exp) (xs : List Bvi.Exp)
    (headIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [x])
    (tailIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc xs) :
    scanSound (C := C) (F := F) ctx loc (x :: xs) := by
  intro env state next values related run
  change BviSem.evaluateTuple (x :: xs, env, state) = _ at run
  rw [BviSem.evaluateCons] at run
  cases first : BviSem.evaluate [x] env state with
  | mk result middle =>
    cases result with
    | err error => simp [BviSem.evaluateTuple, first] at run
    | val headValues =>
      obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton x env state middle headValues first
      cases rest : BviSem.evaluate xs env middle with
      | mk tailResult last =>
        cases tailResult with
        | err error => simp [BviSem.evaluateTuple, first, rest] at run
        | val tailValues =>
          simp only [BviSem.evaluateTuple, first, rest, Flapjack.holHd,
            Prod.mk.injEq, SemanticPrimitivesHOL.Result.val.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          have headSound := headIH ctx env state middle [value] related first
          simp only [scanExpr_single, List.mem_singleton, forall_eq,
            List.map_cons, List.map_nil] at headSound
          have tailSound := tailIH (scanSing ctx loc x).1 env middle last tailValues headSound.1 rest
          rw [scanExpr_list, scanList.eq_def]
          dsimp only
          rw [← scanExpr_list]
          constructor
          · intro entry mem
            simp only [List.mem_cons] at mem
            rcases mem with rfl | mem
            · exact headSound.1
            · exact tailSound.1 entry mem
          · cases headSound.2 with
            | cons valueSound empty =>
              exact List.Forall₂.cons valueSound tailSound.2

mutual
/-- Every single-expression scan satisfies the source type-soundness
invariant for the current BVI evaluator. -/
theorem scanSound_single {C F : Type} (ctx : List ValueType) (loc : Nat) (e : Bvi.Exp) :
    scanSound (C := C) (F := F) ctx loc [e] := by
  cases e with
  | var n => exact scanSound_var ctx loc n
  | force place index => exact scanSound_force ctx loc place index
  | op op args => exact scanSound_op ctx loc op args
  | tick body => exact scanSound_tick ctx loc body (fun ctx => scanSound_single ctx loc body)
  | ifThenElse condition yes no =>
    exact scanSound_if ctx loc condition yes no
      (fun ctx => scanSound_single ctx loc condition)
      (fun ctx => scanSound_single ctx loc yes)
      (fun ctx => scanSound_single ctx loc no)
  | «let» bindings body =>
    exact scanSound_let ctx loc bindings body
      (fun ctx => scanSound_list ctx loc bindings)
      (fun ctx => scanSound_single ctx loc body)
  | raise e => exact (scanSound_default_cases ctx loc).1 e
  | «return» xs => exact (scanSound_default_cases ctx loc).2.1 xs
  | call ticks dest args handler => exact (scanSound_default_cases ctx loc).2.2.1 ticks dest args handler
  | letCall rets ticks dest args body => exact (scanSound_default_cases ctx loc).2.2.2 rets ticks dest args body
termination_by sizeOf e

/-- Every source-shaped list scan satisfies the type-soundness invariant. -/
theorem scanSound_list {C F : Type} (ctx : List ValueType) (loc : Nat) (xs : List Bvi.Exp) :
    scanSound (C := C) (F := F) ctx loc xs := by
  cases xs with
  | nil => exact scanSound_nil ctx loc
  | cons x xs =>
    exact scanSound_cons ctx loc x xs
      (fun ctx => scanSound_single ctx loc x)
      (fun ctx => scanSound_list ctx loc xs)
termination_by sizeOf xs
end

/-- The source-shaped scan type-soundness theorem. This remains untagged
until the BVI evaluator and dispatcher are reviewed against the source. -/
theorem scanExpr_tyRel {C F : Type} (ts : List ValueType) (loc : Nat) (xs : List Bvi.Exp)
    (env : List Value) (ys : List (List ValueType × ValueType × Bool × Option AssocOp))
    (state next : BviSem.BviState C F) (values : List Value)
    (hyp : tyRel env ts ∧ scanExpr ts loc xs = ys ∧
      BviSem.evaluate xs env state = (.val values, next)) :
    (∀ entry ∈ ys, tyRel env entry.1) ∧ tyRel values (ys.map fun (_, ty, _, _) => ty) := by
  obtain ⟨related, rfl, run⟩ := hyp
  exact scanSound_list ts loc xs env state next values related run

end Flapjack.Compiler.Backend.BviTailrec
