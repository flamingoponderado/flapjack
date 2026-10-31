import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeRelation

/-! State-independent accumulator primitive behavior for the tail-recursion
simulation. The evaluator and dispatcher remain subject to source review. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi BvlSem

/-- Pure value projection of the accumulator primitive dispatcher. -/
def accumulatorApply (op : AssocOp) (args : List Value) : Option Value :=
  match op with
  | .plus => BvlSem.doIntApp .add args
  | .times => BvlSem.doIntApp .mult args
  | .noop => BvlSem.doIntApp .mod args
  | .append => match args with
    | [x, y] => do
      let xs ← valueToList x
      let ys ← valueToList y
      pure (listToValue (xs ++ ys))
    | _ => none

/-- A well-typed accumulator value is unchanged by the source identity on
the right. -/
theorem accumulator_identity_right (op : AssocOp) (value : Value)
    (notNoop : op ≠ .noop) (typed : valueMatchesType value (opType op)) :
    accumulatorApply op [value, opIdValue op] = some value := by
  cases op with
  | plus =>
    obtain ⟨n, rfl⟩ := typed.1 rfl
    simp [accumulatorApply, opIdValue, BvlSem.doIntApp]
  | times =>
    obtain ⟨n, rfl⟩ := typed.1 rfl
    simp [accumulatorApply, opIdValue, BvlSem.doIntApp]
  | append =>
    obtain ⟨xs, decode⟩ := typed.2 rfl
    have encode := listToValue_of_decode value xs decode
    simp [accumulatorApply, opIdValue, valueToList, BackendCommon.nilTag, decode, encode]
  | noop => contradiction

/-- A well-typed accumulator value is unchanged by the source identity on
the left. -/
theorem accumulator_identity_left (op : AssocOp) (value : Value)
    (notNoop : op ≠ .noop) (typed : valueMatchesType value (opType op)) :
    accumulatorApply op [opIdValue op, value] = some value := by
  cases op with
  | plus =>
    obtain ⟨n, rfl⟩ := typed.1 rfl
    simp [accumulatorApply, opIdValue, BvlSem.doIntApp]
  | times =>
    obtain ⟨n, rfl⟩ := typed.1 rfl
    simp [accumulatorApply, opIdValue, BvlSem.doIntApp]
  | append =>
    obtain ⟨xs, decode⟩ := typed.2 rfl
    have encode := listToValue_of_decode value xs decode
    simp [accumulatorApply, opIdValue, valueToList, BackendCommon.nilTag, decode, encode]
  | noop => contradiction

/-- Accumulator dispatch only computes a value; it does not change the BVI
state or inspect the state-dependent compiler fields. -/
theorem doApp_toOp_pure {C F : Type} (op : AssocOp) (args : List Value)
    (state : BviSem.BviState C F) :
    BviSem.doApp (toOp op) args state =
      match accumulatorApply op args with
      | none => .err (.abort .typeError)
      | some value => .val (value, state) := by
  cases op <;> simp [toOp, accumulatorApply, BviSem.doApp, BviSem.doAppFallback,
    BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric, BvlSem.applyBlock]
  case plus =>
    cases h : BvlSem.doIntApp .add args <;> simp [BviSem.fromBvl_toBvl]
  case times =>
    cases h : BvlSem.doIntApp .mult args <;> simp [BviSem.fromBvl_toBvl]
  case noop =>
    cases h : BvlSem.doIntApp .mod args <;> simp [BviSem.fromBvl_toBvl]
  case append =>
    cases args with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
        cases ys with
        | cons z zs => rfl
        | nil =>
          cases hx : valueToList x <;> cases hy : valueToList y <;> simp [hx, hy, BviSem.fromBvl_toBvl]

/-- Successful accumulator dispatch preserves the input state. -/
theorem doApp_toOp_state {C F : Type} (op : AssocOp) (args : List Value)
    (state next : BviSem.BviState C F) (result : Value)
    (run : BviSem.doApp (toOp op) args state = .val (result, next)) : next = state := by
  rw [doApp_toOp_pure] at run
  cases found : accumulatorApply op args with
  | none => simp [found] at run
  | some value =>
    simp [found] at run
    exact run.2.symm

/-- Accumulator dispatch produces the same value in related source and target
states and preserves their relation. -/
theorem stateRel_doApp_toOp {C F : Type} (op : AssocOp) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (result : Value) (related : stateRel source target)
    (run : BviSem.doApp (toOp op) args source = .val (result, sourceNext)) :
    ∃ targetNext, BviSem.doApp (toOp op) args target = .val (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  rw [doApp_toOp_pure] at run
  cases found : accumulatorApply op args with
  | none => simp [found] at run
  | some value =>
    simp [found] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp [doApp_toOp_pure, found], related⟩

/-- Accumulator dispatch errors do not depend on compiler state. -/
theorem doApp_toOp_error {C F D G : Type} (op : AssocOp) (args : List Value)
    (source : BviSem.BviState C F) (target : BviSem.BviState D G)
    (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (toOp op) args source = .err error) :
    BviSem.doApp (toOp op) args target = .err error := by
  rw [doApp_toOp_pure] at run ⊢
  cases found : accumulatorApply op args <;> simp_all

/-- Evaluating in-bounds variable expressions returns the corresponding
environment entries without changing state. -/
theorem evaluate_var_indices {C F : Type} (indices : List Nat) (env : List Value)
    (state : BviSem.BviState C F) (bounds : ∀ n ∈ indices, n < env.length) :
    BviSem.evaluate (indices.map Bvi.Exp.var) env state =
      (.val (indices.map fun n => (env[n]?).getD BvlSem.unitValue), state) := by
  induction indices with
  | nil => simp [BviSem.evaluate]
  | cons n ns ih =>
    have bound : n < env.length := bounds n (by simp)
    have restBounds : ∀ k ∈ ns, k < env.length := by
      intro k member
      exact bounds k (by simp [member])
    have head : BviSem.evaluate [.var n] env state = (.val [env[n]], state) := by
      simp [BviSem.evaluate, bound]
    change BviSem.evaluateTuple (.var n :: ns.map Bvi.Exp.var, env, state) = _
    rw [BviSem.evaluateCons]
    simp [BviSem.evaluateTuple, head, ih restBounds, Flapjack.holHd, bound]

/-- Reading every environment index in order recovers the environment. -/
theorem map_range_environment (env : List Value) :
    (List.range env.length).map (fun n => (env[n]?).getD BvlSem.unitValue) = env := by
  apply List.ext_getElem
  · simp
  · intro n leftBound rightBound
    simp [List.getElem_map, List.getElem_range, rightBound]

/-- The wrapper's variable bindings evaluate to the original environment. -/
theorem evaluate_var_range {C F : Type} (env : List Value) (state : BviSem.BviState C F) :
    BviSem.evaluate ((List.range env.length).map Bvi.Exp.var) env state = (.val env, state) := by
  simpa [map_range_environment] using
    evaluate_var_indices (List.range env.length) env state (by simp)

/-- The source identity expression evaluates to the corresponding identity
value for each optimizing accumulator operator. -/
theorem evaluate_identity {C F : Type} (op : AssocOp) (env : List Value)
    (state : BviSem.BviState C F) (notNoop : op ≠ .noop) :
    BviSem.evaluate [identity op] env state = (.val [opIdValue op], state) := by
  cases op with
  | plus =>
    simpa [identity, opIdValue] using evaluate_smallInt (C := C) (F := F) 0 (by decide) env state
  | times =>
    simpa [identity, opIdValue] using evaluate_smallInt (C := C) (F := F) 1 (by decide) env state
  | append =>
    simpa [identity, opIdValue, BvlSem.listToValue] using evaluate_nil env state
  | noop => contradiction

/-- The wrapper evaluates its worker under the original arguments, followed
by the accumulator identity and the original environment. -/
theorem evaluate_letWrap {C F : Type} (body : Bvi.Exp) (op : AssocOp)
    (env : List Value) (state : BviSem.BviState C F) (notNoop : op ≠ .noop) :
    BviSem.evaluate [letWrap env.length (identity op) body] env state =
      BviSem.evaluate [body] (env ++ [opIdValue op] ++ env) state := by
  have bindings : BviSem.evaluate (((List.range env.length).map Bvi.Exp.var) ++ [identity op]) env state =
      (.val (env ++ [opIdValue op]), state) := by
    change BviSem.evaluateTuple (((List.range env.length).map Bvi.Exp.var) ++ [identity op], env, state) = _
    rw [BviSem.evaluateAppend]
    simp [BviSem.evaluateTuple, evaluate_var_range, evaluate_identity op env state notNoop]
  change BviSem.evaluate [.let (((List.range env.length).map Bvi.Exp.var) ++ [identity op]) body] env state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, bindings]

/-- The wrapper's extended environment satisfies the accumulator relation
with the accumulator at the first position after the original arguments. -/
theorem envRel_initial (op : AssocOp) (env : List Value) (notNoop : op ≠ .noop) :
    envRel (opType op) true env.length env (env ++ [opIdValue op] ++ env) := by
  cases op <;> simp_all [envRel, opType, opIdValue, valueToList, BackendCommon.nilTag]

end Flapjack.Compiler.Backend.BviTailrec
