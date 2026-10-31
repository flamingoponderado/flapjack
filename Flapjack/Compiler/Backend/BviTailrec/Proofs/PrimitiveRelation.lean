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

/-- Updating related states with the same reference map preserves the state
relation. -/
theorem stateRel_withRefs {C F : Type} (source : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (refs : HolFiniteMapExact Nat (Ref Value))
    (related : stateRel source target) :
    stateRel { source with refs := refs } { target with refs := refs } := by
  rcases related with ⟨_, clock, global, ffi, oracle, compiler, code, ns, input, bound⟩
  exact ⟨rfl, clock, global, ffi, oracle, compiler, code, ns, input, bound⟩

/-- Updating related states with the same global pointer preserves the state
relation. -/
theorem stateRel_withGlobal {C F : Type} (source : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (global : Option Nat)
    (related : stateRel source target) :
    stateRel { source with global := global } { target with global := global } := by
  rcases related with ⟨refs, clock, _, ffi, oracle, compiler, code, ns, input, bound⟩
  exact ⟨refs, clock, rfl, ffi, oracle, compiler, code, ns, input, bound⟩

/-- Updating related states with the same FFI state preserves the state
relation. -/
theorem stateRel_withFfi {C F : Type} (source : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (ffi : HolFfiState F)
    (related : stateRel source target) :
    stateRel { source with ffi := ffi } { target with ffi := ffi } := by
  rcases related with ⟨refs, clock, global, _, oracle, compiler, code, ns, input, bound⟩
  exact ⟨refs, clock, global, rfl, oracle, compiler, code, ns, input, bound⟩

/-- Successful label primitives preserve related states and produce the same
code pointer. The source code relation guarantees the label exists on the
target even when its body has been rewritten. -/
theorem stateRel_doApp_label {C F : Type} (label : Nat) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (result : Value) (related : stateRel source target)
    (run : BviSem.doApp (.label label) args source = .val (result, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.label label) args target = .val (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  cases args with
  | cons value rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | nil =>
    cases sourceLookup : sptLookup label source.code with
    | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceLookup] at run
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      obtain ⟨compiled, targetLookup⟩ :=
        codeRel_lookup_exists source.code target.code (stateRel_codeRel source target related)
          label arity body sourceLookup
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceLookup] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨target, by simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, targetLookup], related⟩

/-- A label primitive can fail only with the source type error. -/
theorem doApp_label_error {C F : Type} (label : Nat) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.label label) args state = .err error) : error = .abort .typeError := by
  cases args with
  | cons value rest => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
  | nil =>
    cases lookup : sptLookup label state.code with
    | none => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, lookup] using run.symm
    | some entry => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, lookup] at run

/-- Small-integer constants execute identically in related states. -/
theorem stateRel_doApp_intConst {C F : Type} (number : Int) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (result : Value) (related : stateRel source target)
    (run : BviSem.doApp (.intOp (.const number)) args source = .val (result, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.intOp (.const number)) args target = .val (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  cases args with
  | cons value rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | nil =>
    by_cases small : BackendCommon.smallEnoughInt number
    · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, small] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨target, by simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, small], related⟩
    · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, small] at run

/-- Successful global-pointer reads agree in related states. -/
theorem stateRel_doApp_globalsPtr {C F : Type} (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (result : Value) (related : stateRel source target)
    (run : BviSem.doApp (.globOp .globalsPtr) args source = .val (result, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.globOp .globalsPtr) args target = .val (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  cases args with
  | cons value rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | nil =>
    cases pointer : source.global with
    | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer] at run
    | some ptr =>
      have targetPointer : target.global = some ptr := by simpa [pointer] using (stateRel_const source target related).2.2.1
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨target, by simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, targetPointer], related⟩

/-- Successful global-pointer writes update both related states identically. -/
theorem stateRel_doApp_setGlobalsPtr {C F : Type} (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (result : Value) (related : stateRel source target)
    (run : BviSem.doApp (.globOp .setGlobalsPtr) args source = .val (result, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.globOp .setGlobalsPtr) args target = .val (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons value rest =>
    cases rest with
    | cons v vs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | nil =>
      cases value with
      | refPtr flag ptr =>
        cases flag with
        | false => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        | true =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
          obtain ⟨rfl, rfl⟩ := run
          exact ⟨{ target with global := some ptr },
            by simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux],
            stateRel_withGlobal source target (some ptr) related⟩
      | _ => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run

/-- Integer-constant primitives report only the source type error. -/
theorem doApp_intConst_error {C F : Type} (number : Int) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.intOp (.const number)) args state = .err error) : error = .abort .typeError := by
  cases args with
  | cons value rest => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
  | nil =>
    by_cases small : BackendCommon.smallEnoughInt number
    · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, small] at run
    · simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, small] using run.symm

/-- A global-pointer read reports only the source type error. -/
theorem doApp_globalsPtr_error {C F : Type} (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.globOp .globalsPtr) args state = .err error) : error = .abort .typeError := by
  cases args with
  | cons value rest => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
  | nil =>
    cases pointer : state.global with
    | none => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer] using run.symm
    | some ptr => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer] at run

/-- A global-pointer write reports only the source type error. -/
theorem doApp_setGlobalsPtr_error {C F : Type} (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.globOp .setGlobalsPtr) args state = .err error) : error = .abort .typeError := by
  cases args with
  | nil => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
  | cons value rest =>
    cases rest with
    | cons v vs => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
    | nil =>
      cases value with
      | refPtr flag ptr =>
        cases flag with
        | false => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
        | true => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | _ => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm

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
