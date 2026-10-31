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

/-- Combining two well-typed accumulator values succeeds and retains the
operator's required type. -/
theorem accumulator_typed (op : AssocOp) (x y : Value) (notNoop : op ≠ .noop)
    (tx : valueMatchesType x (opType op)) (ty : valueMatchesType y (opType op)) :
    ∃ value, accumulatorApply op [x, y] = some value ∧ valueMatchesType value (opType op) := by
  cases op with
  | plus =>
    obtain ⟨a, rfl⟩ := tx.1 rfl
    obtain ⟨b, rfl⟩ := ty.1 rfl
    exact ⟨.number (a + b), by simp [accumulatorApply, BvlSem.doIntApp], by simp [valueMatchesType, opType]⟩
  | times =>
    obtain ⟨a, rfl⟩ := tx.1 rfl
    obtain ⟨b, rfl⟩ := ty.1 rfl
    exact ⟨.number (a * b), by simp [accumulatorApply, BvlSem.doIntApp], by simp [valueMatchesType, opType]⟩
  | append =>
    obtain ⟨xs, hx⟩ := tx.2 rfl
    obtain ⟨ys, hy⟩ := ty.2 rfl
    exact ⟨listToValue (xs ++ ys), by simp [accumulatorApply, hx, hy],
      by simp [valueMatchesType, opType, valueToList_listToValue]⟩
  | noop => contradiction

/-- The accumulator operations associate on values of their required type.
This supplies the algebraic step for moving an accumulator across a recursive
call. -/
theorem accumulator_associative (op : AssocOp) (x y z : Value)
    (notNoop : op ≠ .noop) (tx : valueMatchesType x (opType op))
    (ty : valueMatchesType y (opType op)) (tz : valueMatchesType z (opType op)) :
    ∃ xy yz result, accumulatorApply op [x, y] = some xy ∧
      accumulatorApply op [y, z] = some yz ∧
      accumulatorApply op [xy, z] = some result ∧
      accumulatorApply op [x, yz] = some result := by
  cases op with
  | plus =>
    obtain ⟨a, rfl⟩ := tx.1 rfl
    obtain ⟨b, rfl⟩ := ty.1 rfl
    obtain ⟨c, rfl⟩ := tz.1 rfl
    refine ⟨.number (a + b), .number (b + c), .number ((a + b) + c), ?_, ?_, ?_, ?_⟩
    all_goals simp [accumulatorApply, BvlSem.doIntApp, Int.add_assoc]
  | times =>
    obtain ⟨a, rfl⟩ := tx.1 rfl
    obtain ⟨b, rfl⟩ := ty.1 rfl
    obtain ⟨c, rfl⟩ := tz.1 rfl
    refine ⟨.number (a * b), .number (b * c), .number ((a * b) * c), ?_, ?_, ?_, ?_⟩
    all_goals simp [accumulatorApply, BvlSem.doIntApp, Int.mul_assoc]
  | append =>
    obtain ⟨xs, hx⟩ := tx.2 rfl
    obtain ⟨ys, hy⟩ := ty.2 rfl
    obtain ⟨zs, hz⟩ := tz.2 rfl
    refine ⟨listToValue (xs ++ ys), listToValue (ys ++ zs), listToValue ((xs ++ ys) ++ zs),
      ?_, ?_, ?_, ?_⟩
    all_goals simp [accumulatorApply, hx, hy, hz, valueToList_listToValue, List.append_assoc]
  | noop => contradiction

/-- Reassociation also preserves failure when the recursive result is not
well typed, provided the two accumulated operands are well typed. -/
theorem accumulator_associative_partial (op : AssocOp) (x y z : Value)
    (notNoop : op ≠ .noop) (ty : valueMatchesType y (opType op))
    (tz : valueMatchesType z (opType op)) :
    ∃ yz, accumulatorApply op [y, z] = some yz ∧
      (accumulatorApply op [x, y] >>= fun xy => accumulatorApply op [xy, z]) =
        accumulatorApply op [x, yz] := by
  cases op with
  | plus =>
    obtain ⟨b, rfl⟩ := ty.1 rfl
    obtain ⟨c, rfl⟩ := tz.1 rfl
    refine ⟨.number (b + c), by simp [accumulatorApply, BvlSem.doIntApp], ?_⟩
    cases x <;> simp [accumulatorApply, BvlSem.doIntApp, Int.add_assoc]
  | times =>
    obtain ⟨b, rfl⟩ := ty.1 rfl
    obtain ⟨c, rfl⟩ := tz.1 rfl
    refine ⟨.number (b * c), by simp [accumulatorApply, BvlSem.doIntApp], ?_⟩
    cases x <;> simp [accumulatorApply, BvlSem.doIntApp, Int.mul_assoc]
  | append =>
    obtain ⟨ys, hy⟩ := ty.2 rfl
    obtain ⟨zs, hz⟩ := tz.2 rfl
    refine ⟨listToValue (ys ++ zs), by simp [accumulatorApply, hy, hz], ?_⟩
    cases hx : valueToList x with
    | none => simp [accumulatorApply, hx]
    | some xs => simp [accumulatorApply, hx, hy, hz, valueToList_listToValue, List.append_assoc]
  | noop => contradiction

/-- The integer accumulator operations are commutative, as required when
the source rewrite swaps a recursive left operand. List append is excluded. -/
theorem accumulator_commutative (op : AssocOp) (x y : Value)
    (notNoop : op ≠ .noop) (notAppend : op ≠ .append)
    (tx : valueMatchesType x (opType op)) (ty : valueMatchesType y (opType op)) :
    accumulatorApply op [x, y] = accumulatorApply op [y, x] := by
  cases op with
  | plus =>
    obtain ⟨a, rfl⟩ := tx.1 rfl
    obtain ⟨b, rfl⟩ := ty.1 rfl
    simp [accumulatorApply, BvlSem.doIntApp, Int.add_comm]
  | times =>
    obtain ⟨a, rfl⟩ := tx.1 rfl
    obtain ⟨b, rfl⟩ := ty.1 rfl
    simp [accumulatorApply, BvlSem.doIntApp, Int.mul_comm]
  | append => contradiction
  | noop => contradiction

/-- The integer accumulator operations are commutative even on malformed
operands, where both orders produce the same failure. -/
theorem accumulator_commutative_all (op : AssocOp) (x y : Value)
    (notNoop : op ≠ .noop) (notAppend : op ≠ .append) :
    accumulatorApply op [x, y] = accumulatorApply op [y, x] := by
  cases op with
  | plus => cases x <;> cases y <;> simp [accumulatorApply, BvlSem.doIntApp, Int.add_comm]
  | times => cases x <;> cases y <;> simp [accumulatorApply, BvlSem.doIntApp, Int.mul_comm]
  | append => contradiction
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

/-- Pure integer-primitive result, including BVI's bounded constant rule. -/
def intPrimitiveResult (op : ClosLang.IntOp) (args : List Value) : Option Value :=
  match op, args with
  | .const number, [] => if BackendCommon.smallEnoughInt number then some (.number number) else none
  | .const _, _ => none
  | _, _ => BvlSem.doIntApp op args

/-- Integer primitive dispatch is independent of BVI state and leaves it
unchanged whenever it succeeds. -/
theorem doApp_intOp_pure {C F : Type} (op : ClosLang.IntOp) (args : List Value)
    (state : BviSem.BviState C F) :
    BviSem.doApp (.intOp op) args state =
      match intPrimitiveResult op args with
      | none => .err (.abort .typeError)
      | some value => .val (value, state) := by
  have convert (found : Option Value) :
      (match (match found.map (fun value => (value, BviSem.toBvl state)) with
        | none => .err (.abort .typeError)
        | some pair => .val pair : SemanticPrimitivesHOL.Result (Value × BvlSem.State C F) Value) with
       | .val (value, next) => .val (value, BviSem.fromBvl next state)
       | .err (.abort error) => .err (.abort error)
       | .err (.raise value) => .err (.raise (.exn value)) :
         SemanticPrimitivesHOL.Result (Value × BviSem.BviState C F) BviSem.ExnOrRet) =
      (match found with
       | none => .err (.abort .typeError)
       | some value => .val (value, state)) := by
    cases found <;> simp [BviSem.fromBvl_toBvl]
  cases op with
  | const number =>
    cases args <;> by_cases small : BackendCommon.smallEnoughInt number <;>
      simp [intPrimitiveResult, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, small]
  | _ =>
    all_goals simp only [intPrimitiveResult, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric]
    all_goals exact convert _

/-- Integer primitive application preserves state relations, including the
source type-error outcome. -/
theorem stateRel_doApp_intOp {C F : Type} (op : ClosLang.IntOp) (args : List Value)
    (source : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel source target) :
    (BviSem.doApp (.intOp op) args source = .err (.abort .typeError) ∧
      BviSem.doApp (.intOp op) args target = .err (.abort .typeError)) ∨
    ∃ value, BviSem.doApp (.intOp op) args source = .val (value, source) ∧
      BviSem.doApp (.intOp op) args target = .val (value, target) ∧ stateRel source target := by
  rw [doApp_intOp_pure, doApp_intOp_pure]
  cases h : intPrimitiveResult op args with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some value => exact Or.inr ⟨value, rfl, rfl, related⟩

/-- Successful integer primitives preserve related states. -/
theorem stateRel_doApp_intOp_success {C F : Type} (op : ClosLang.IntOp) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (run : BviSem.doApp (.intOp op) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.intOp op) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  rcases stateRel_doApp_intOp op args source target related with failed | ⟨v, sourceRun, targetRun, rel⟩
  · rw [failed.1] at run
    contradiction
  · rw [sourceRun] at run
    cases run
    exact ⟨target, targetRun, rel⟩

/-- Every integer primitive error is the source type error. -/
theorem doApp_intOp_error {C F : Type} (op : ClosLang.IntOp) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.intOp op) args state = .err error) : error = .abort .typeError := by
  rw [doApp_intOp_pure] at run
  cases found : intPrimitiveResult op args with
  | none => simpa [found] using run.symm
  | some value => simp [found] at run

/-- Word primitive dispatch is pure and leaves the BVI state unchanged. -/
theorem doApp_wordOp_pure {C F : Type} (op : ClosLang.WordOp) (args : List Value)
    (state : BviSem.BviState C F) :
    BviSem.doApp (.wordOp op) args state =
      match BvlSem.doWordApp op args with
      | none => .err (.abort .typeError)
      | some value => .val (value, state) := by
  simp only [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
    BvlSem.doApp, BvlSem.applyNumeric]
  cases found : BvlSem.doWordApp op args <;> simp [BviSem.fromBvl_toBvl]

/-- Successful word operations preserve related states. -/
theorem stateRel_doApp_wordOp_success {C F : Type} (op : ClosLang.WordOp) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (run : BviSem.doApp (.wordOp op) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.wordOp op) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  rw [doApp_wordOp_pure] at run ⊢
  cases found : BvlSem.doWordApp op args with
  | none => simp [found] at run
  | some result =>
    simp [found] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp, related⟩

/-- Every word primitive error is the source type error. -/
theorem doApp_wordOp_error {C F : Type} (op : ClosLang.WordOp) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.wordOp op) args state = .err error) : error = .abort .typeError := by
  rw [doApp_wordOp_pure] at run
  cases found : BvlSem.doWordApp op args with
  | none => simpa [found] using run.symm
  | some value => simp [found] at run

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

/-- Byte-array allocation preserves the related reference stores, including
the fresh reference, initial contents, and mutability flag. -/
theorem stateRel_doApp_refByte {C F : Type} (flag : Bool) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (run : BviSem.doApp (.memOp (.refByte flag)) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.memOp (.refByte flag)) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  have refs := (stateRel_const source target related).1
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | cons b rest =>
      cases rest with
      | cons extra xs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | nil =>
        cases a <;> cases b <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        rename_i count byte
        by_cases neg : count < 0
        · simp [neg] at run
        · cases converted : ClosSem.intToByte byte with
          | none => simp [neg, converted] at run
          | some byteValue =>
            simp [neg, converted] at run
            obtain ⟨rfl, rfl⟩ := run
            let ptr := leastUnusedRef source.refs
            let entry : Ref Value := Ref.byteArray flag (List.replicate count.toNat byteValue)
            refine ⟨{ target with refs := source.refs.updateEq (ptr, entry) }, ?_,
              stateRel_withRefs source target _ related⟩
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, refs, neg, converted, ptr, entry]

/-- Byte-array allocation can fail only with a type error. -/
theorem doApp_refByte_error {C F : Type} (flag : Bool) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.memOp (.refByte flag)) args state = .err error) : error = .abort .typeError := by
  cases args with
  | nil => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
  | cons a rest =>
    cases rest with
    | nil => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
    | cons b rest =>
      cases rest with
      | cons extra xs => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
      | nil =>
        cases a <;> cases b <;>
          try (simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm)
        rename_i count byte
        by_cases neg : count < 0
        · simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, neg] using run.symm
        · cases converted : ClosSem.intToByte byte with
          | none => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, neg, converted] using run.symm
          | some byteValue => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, neg, converted] at run

/-- The result of finalising a mutable block depends only on its input value
and the shared reference store. -/
noncomputable def finaliseConsEffect (args : List Value) (refs : HolFiniteMapExact Nat (Ref Value)) :
    Option (Value × HolFiniteMapExact Nat (Ref Value)) :=
  match args with
  | [value] => BviSem.finaliseCons value refs
  | _ => none

/-- Finalisation updates only the reference store; malformed arguments are
rejected by the BVL fallback. -/
theorem doApp_finaliseCons_effect {C F : Type} (args : List Value) (state : BviSem.BviState C F) :
    BviSem.doApp (.memOp .finaliseCons) args state =
      match finaliseConsEffect args state.refs with
      | none => .err (.abort .typeError)
      | some (value, refs) => .val (value, { state with refs := refs }) := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyMemory, finaliseConsEffect]
  | cons value rest =>
    cases rest with
    | cons x xs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyMemory, finaliseConsEffect]
    | nil =>
      simp only [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, finaliseConsEffect]
      cases result : BviSem.finaliseCons value state.refs with
      | none => simp
      | some pair => cases pair; simp

/-- Finalisation preserves related states. -/
theorem stateRel_doApp_finaliseCons {C F : Type} (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (run : BviSem.doApp (.memOp .finaliseCons) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.memOp .finaliseCons) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  have refs := (stateRel_const source target related).1
  rw [doApp_finaliseCons_effect] at run ⊢
  rw [refs]
  cases effect : finaliseConsEffect args source.refs with
  | none => simp [effect] at run
  | some pair =>
    obtain ⟨result, newRefs⟩ := pair
    simp [effect] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨{ target with refs := newRefs }, by simp, stateRel_withRefs source target newRefs related⟩

/-- Finalisation reports only type errors. -/
theorem doApp_finaliseCons_error {C F : Type} (args : List Value) (state : BviSem.BviState C F)
    (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.memOp .finaliseCons) args state = .err error) : error = .abort .typeError := by
  rw [doApp_finaliseCons_effect] at run
  cases effect : finaliseConsEffect args state.refs with
  | none => simpa [effect] using run.symm
  | some pair => cases pair; simp [effect] at run

/-- The reference-store effect of a mutable-block update. -/
def updateConsEffect (args : List Value) (refs : HolFiniteMapExact Nat (Ref Value)) :
    Option (HolFiniteMapExact Nat (Ref Value)) :=
  match args with
  | [.refPtr _ ptr, .number index, value] =>
    match refs.lookup ptr with
    | some (.mutBlock tag finalised left _ right) =>
      if index ≠ Int.ofNat left.length ∨ finalised then none
      else some (refs.updateEq (ptr, .mutBlock tag false left value right))
    | _ => none
  | _ => none

/-- Mutable-block updates either fail with a type error or update only the
reference store. Malformed arguments reach the BVL fallback and fail there. -/
theorem doApp_updateCons_effect {C F : Type} (args : List Value) (state : BviSem.BviState C F) :
    BviSem.doApp (.memOp .updateCons) args state =
      match updateConsEffect args state.refs with
      | none => .err (.abort .typeError)
      | some refs => .val (unitValue, { state with refs := refs }) := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyMemory, updateConsEffect]
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyMemory, updateConsEffect]
    | cons b rest =>
      cases rest with
      | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BvlSem.applyMemory, updateConsEffect]
      | cons value rest =>
        cases rest with
        | cons x xs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
            BvlSem.applyMemory, updateConsEffect]
        | nil =>
          cases a <;> cases b <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
            BvlSem.doApp, BvlSem.applyMemory, updateConsEffect]
          rename_i flag ptr index
          cases found : state.refs.lookup ptr with
          | none => simp
          | some entry =>
            cases entry <;> simp
            rename_i tag finalised left old right
            by_cases same : index = Int.ofNat left.length <;> cases finalised <;> simp_all

/-- Mutable-block updates preserve related stores. -/
theorem stateRel_doApp_updateCons {C F : Type} (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (run : BviSem.doApp (.memOp .updateCons) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.memOp .updateCons) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  have refs := (stateRel_const source target related).1
  rw [doApp_updateCons_effect] at run ⊢
  rw [refs]
  cases effect : updateConsEffect args source.refs with
  | none => simp [effect] at run
  | some newRefs =>
    simp [effect] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨{ target with refs := newRefs }, by simp, stateRel_withRefs source target newRefs related⟩

/-- Mutable-block updates report only type errors. -/
theorem doApp_updateCons_error {C F : Type} (args : List Value) (state : BviSem.BviState C F)
    (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.memOp .updateCons) args state = .err error) : error = .abort .typeError := by
  rw [doApp_updateCons_effect] at run
  cases effect : updateConsEffect args state.refs with
  | none => simpa [effect] using run.symm
  | some refs => simp [effect] at run

/-- Mutable-block allocation chooses the same fresh reference and installs
the same entry in related reference stores. -/
theorem stateRel_doApp_mutCons {C F : Type} (tag index : Nat) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (run : BviSem.doApp (.memOp (.mutCons tag index)) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.memOp (.mutCons tag index)) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  have refs := (stateRel_const source target related).1
  cases selected : args[index]? with
  | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, selected] at run
  | some child =>
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, selected] at run
    obtain ⟨rfl, rfl⟩ := run
    let ptr := leastUnusedRef source.refs
    let entry := Ref.mutBlock tag false (args.take index) child (args.drop (index + 1))
    refine ⟨{ target with refs := source.refs.updateEq (ptr, entry) }, ?_,
      stateRel_withRefs source target _ related⟩
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, selected, refs, ptr, entry]

/-- Mutable-block allocation can fail only with a type error. -/
theorem doApp_mutCons_error {C F : Type} (tag index : Nat) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.memOp (.mutCons tag index)) args state = .err error) :
    error = .abort .typeError := by
  cases selected : args[index]? with
  | none => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, selected] using run.symm
  | some child => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, selected] at run

/-- The BVI global allocation primitive always reports a type error. -/
theorem doApp_allocGlobal {C F : Type} (args : List Value) (state : BviSem.BviState C F) :
    BviSem.doApp (.globOp .allocGlobal) args state = .err (.abort .typeError) := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux]

/-- BVL block operations depend only on the reference store and update only that store. -/
theorem applyBlock_sharedRefs {C D F G : Type} (op : ClosLang.BlockOp) (args : List Value)
    (s : BvlSem.State C F) (t : BvlSem.State D G) (refs : t.refs = s.refs) :
    BvlSem.applyBlock op args t = (BvlSem.applyBlock op args s).map
      (fun (value, next) => (value, { t with refs := next.refs })) := by
  unfold BvlSem.applyBlock
  rw [refs]
  repeat' split
  all_goals simp_all [Option.map_bind]
  all_goals cases t; simp_all
/-- BVI delegates block operations other than fromList to BVL. -/
theorem doApp_block_viaBvl {C F : Type} (op : ClosLang.BlockOp) (args : List Value) (s : BviSem.BviState C F)
    (notFromList : ∀ tag, op ≠ .fromList tag) :
    BviSem.doApp (.blockOp op) args s =
      match BvlSem.applyBlock op args (BviSem.toBvl s) with
      | none => .err (.abort .typeError)
      | some (value, next) => .val (value, BviSem.fromBvl next s) := by
  cases op <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at *
  all_goals split <;> simp_all
  all_goals split <;> simp_all
/-- Delegated block operations preserve related BVI states. -/
theorem stateRel_doApp_block_viaBvl {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (notFromList : ∀ tag, op ≠ .fromList tag)
    (run : BviSem.doApp (.blockOp op) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.blockOp op) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  have refs := (stateRel_const source target related).1
  have eqRefs : (BviSem.toBvl target).refs = (BviSem.toBvl source).refs := by simpa [BviSem.toBvl] using refs
  have transfer := applyBlock_sharedRefs op args (BviSem.toBvl source) (BviSem.toBvl target) eqRefs
  have self := applyBlock_sharedRefs op args (BviSem.toBvl source) (BviSem.toBvl source) rfl
  rw [doApp_block_viaBvl op args source notFromList] at run
  rw [doApp_block_viaBvl op args target notFromList]
  cases found : BvlSem.applyBlock op args (BviSem.toBvl source) with
  | none => simp [found] at run
  | some pair =>
    obtain ⟨v, next⟩ := pair
    simp only [found, Option.map_some] at self transfer
    have nextEq : next = { BviSem.toBvl source with refs := next.refs } := by
      exact (Prod.mk.inj (Option.some.inj self)).2
    rw [found] at run
    dsimp only at run
    rw [nextEq] at run
    simp [BviSem.toBvl, BviSem.fromBvl] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨{ target with refs := next.refs }, ?_, stateRel_withRefs source target next.refs related⟩
    rw [transfer]
    simp [BviSem.toBvl, BviSem.fromBvl]
/-- Delegated block operations report only type errors. -/
theorem doApp_block_viaBvl_error {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state : BviSem.BviState C F) (notFromList : ∀ tag, op ≠ .fromList tag)
    (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.blockOp op) args state = .err error) : error = .abort .typeError := by
  rw [doApp_block_viaBvl op args state notFromList] at run
  cases found : BvlSem.applyBlock op args (BviSem.toBvl state) with
  | none => simpa [found] using run.symm
  | some pair => cases pair; simp [found] at run

/-- BVL memory operations depend only on the reference store and update only that store. -/
theorem applyMemory_sharedRefs {C D F G : Type} (op : ClosLang.MemOp) (args : List Value)
    (s : BvlSem.State C F) (t : BvlSem.State D G) (refs : t.refs = s.refs) :
    BvlSem.applyMemory op args t = (BvlSem.applyMemory op args s).map
      (fun (value, next) => (value, { t with refs := next.refs })) := by
  unfold BvlSem.applyMemory
  rw [refs]
  repeat' split
  all_goals simp_all [Option.map_bind]
  all_goals try (cases t; simp_all)
  all_goals try (repeat' (congr 1; funext value; cases value <;> simp [Option.map_bind]))
/-- Memory operators rejected directly by the BVI dispatcher. -/
def memoryRejected : ClosLang.MemOp → Bool
  | .fromListByte | .toListByte | .concatByteVec | .copyByte true => true
  | _ => false

/-- These BVI memory operations always report a type error after their
arguments have been evaluated. -/
theorem doApp_memory_rejected {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state : BviSem.BviState C F) (rejected : memoryRejected op = true) :
    BviSem.doApp (.memOp op) args state = .err (.abort .typeError) := by
  cases op with
  | copyByte flag => cases flag <;> simp [memoryRejected, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at *
  | _ => all_goals simp [memoryRejected, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at *

/-- Memory operators whose BVI dispatcher unconditionally delegates to BVL. -/
def memoryDelegated : ClosLang.MemOp → Bool
  | .refByte _ | .mutCons _ _ | .updateCons | .finaliseCons | .fromListByte | .toListByte | .concatByteVec | .copyByte true => false
  | _ => true
/-- BVI memory operators in the delegated class use the BVL dispatcher. -/
theorem doApp_memory_viaBvl {C F : Type} (op : ClosLang.MemOp) (args : List Value) (s : BviSem.BviState C F)
    (h : memoryDelegated op = true) :
    BviSem.doApp (.memOp op) args s =
      match BvlSem.applyMemory op args (BviSem.toBvl s) with
      | none => .err (.abort .typeError)
      | some (value, next) => .val (value, BviSem.fromBvl next s) := by
  cases op with
  | copyByte flag =>
    cases flag <;> simp [memoryDelegated, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at *
    all_goals split <;> simp_all
    all_goals split <;> simp_all
  | _ =>
    all_goals simp [memoryDelegated, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at *
    all_goals split <;> simp_all
    all_goals split <;> simp_all
/-- Delegated memory operations preserve related BVI states. -/
theorem stateRel_doApp_memory_viaBvl {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (delegated : memoryDelegated op = true)
    (run : BviSem.doApp (.memOp op) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.memOp op) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  have refs := (stateRel_const source target related).1
  have eqRefs : (BviSem.toBvl target).refs = (BviSem.toBvl source).refs := by simpa [BviSem.toBvl] using refs
  have transfer := applyMemory_sharedRefs op args (BviSem.toBvl source) (BviSem.toBvl target) eqRefs
  have self := applyMemory_sharedRefs op args (BviSem.toBvl source) (BviSem.toBvl source) rfl
  rw [doApp_memory_viaBvl op args source delegated] at run
  rw [doApp_memory_viaBvl op args target delegated]
  cases found : BvlSem.applyMemory op args (BviSem.toBvl source) with
  | none => simp [found] at run
  | some pair =>
    obtain ⟨v, next⟩ := pair
    simp only [found, Option.map_some] at self transfer
    have nextEq : next = { BviSem.toBvl source with refs := next.refs } := by
      exact (Prod.mk.inj (Option.some.inj self)).2
    rw [found] at run
    dsimp only at run
    rw [nextEq] at run
    simp [BviSem.toBvl, BviSem.fromBvl] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨{ target with refs := next.refs }, ?_, stateRel_withRefs source target next.refs related⟩
    rw [transfer]
    simp [BviSem.toBvl, BviSem.fromBvl]
/-- Delegated memory operations report only type errors. -/
theorem doApp_memory_viaBvl_error {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state : BviSem.BviState C F) (delegated : memoryDelegated op = true)
    (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.memOp op) args state = .err error) : error = .abort .typeError := by
  rw [doApp_memory_viaBvl op args state delegated] at run
  cases found : BvlSem.applyMemory op args (BviSem.toBvl state) with
  | none => simpa [found] using run.symm
  | some pair => cases pair; simp [found] at run

/-- Constructing a plain block returns its fields without changing state. -/
theorem doApp_blockCons {C F : Type} (tag : Nat) (args : List Value) (state : BviSem.BviState C F) :
    BviSem.doApp (.blockOp (.cons tag)) args state = .val (.block tag args, state) := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyBlock, BviSem.fromBvl_toBvl]

/-- Plain block construction preserves related states. -/
theorem stateRel_doApp_blockCons {C F : Type} (tag : Nat) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (run : BviSem.doApp (.blockOp (.cons tag)) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.blockOp (.cons tag)) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  rw [doApp_blockCons] at run
  cases run
  exact ⟨target, doApp_blockCons tag args target, related⟩

/-- Plain block construction cannot report an error. -/
theorem doApp_blockCons_error {C F : Type} (tag : Nat) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.blockOp (.cons tag)) args state = .err error) : error = .abort .typeError := by
  rw [doApp_blockCons] at run
  contradiction

/-- A constant-block build returns the value and reference store produced by
the shared builder; nonempty argument lists are rejected. -/
theorem doApp_blockBuild_effect {C F : Type} (parts : List ClosLang.ConstPart)
    (args : List Value) (state : BviSem.BviState C F) :
    BviSem.doApp (.blockOp (.build parts)) args state =
      match args with
      | [] => let (value, refs) := doBuildConst parts state.refs
        .val (value, { state with refs := refs })
      | _ => .err (.abort .typeError) := by
  cases args with
  | nil =>
    cases built : doBuildConst parts state.refs with
    | mk value refs =>
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyBlock, BviSem.toBvl, BviSem.fromBvl, built]
  | cons value rest =>
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock]

/-- Building a constant block preserves related states. -/
theorem stateRel_doApp_blockBuild {C F : Type} (parts : List ClosLang.ConstPart) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (run : BviSem.doApp (.blockOp (.build parts)) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.blockOp (.build parts)) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  have refs := (stateRel_const source target related).1
  rw [doApp_blockBuild_effect] at run ⊢
  rw [refs]
  cases args with
  | cons head tail => simp at run
  | nil =>
    cases built : doBuildConst parts source.refs with
    | mk builtValue newRefs =>
      simp [built] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨{ target with refs := newRefs }, by simp, stateRel_withRefs source target newRefs related⟩

/-- Constant-block construction reports only type errors. -/
theorem doApp_blockBuild_error {C F : Type} (parts : List ClosLang.ConstPart) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.blockOp (.build parts)) args state = .err error) : error = .abort .typeError := by
  rw [doApp_blockBuild_effect] at run
  cases args with
  | cons head tail => simpa using run.symm
  | nil => cases built : doBuildConst parts state.refs; simp [built] at run

/-- Value computed by BVI's two-argument block-from-list primitive. -/
def blockFromListValue (tag : Nat) (args : List Value) : Option Value :=
  match args with
  | [.number length, list] => do
    let values ← valueToList list
    if length = Int.ofNat values.length then some (.block tag values) else none
  | _ => none

/-- Constructing a block from a list is pure in BVI; the length check is part
of the source dispatcher. -/
theorem doApp_blockFromList_pure {C F : Type} (tag : Nat) (args : List Value)
    (state : BviSem.BviState C F) :
    BviSem.doApp (.blockOp (.fromList tag)) args state =
      match blockFromListValue tag args with
      | none => .err (.abort .typeError)
      | some value => .val (value, state) := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, blockFromListValue]
  | cons length rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, blockFromListValue]
    | cons list rest =>
      cases rest with
      | cons extra xs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, blockFromListValue]
      | nil =>
        cases length <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, blockFromListValue]
        rename_i n
        cases decoded : valueToList list with
        | none => simp
        | some values =>
          split <;> simp_all

/-- Successful block-from-list operations preserve related states. -/
theorem stateRel_doApp_blockFromList {C F : Type} (tag : Nat) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (value : Value) (related : stateRel source target)
    (run : BviSem.doApp (.blockOp (.fromList tag)) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.blockOp (.fromList tag)) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  rw [doApp_blockFromList_pure] at run ⊢
  cases found : blockFromListValue tag args with
  | none => simp [found] at run
  | some result =>
    simp [found] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp, related⟩

/-- Block-from-list failures are type errors. -/
theorem doApp_blockFromList_error {C F : Type} (tag : Nat) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.blockOp (.fromList tag)) args state = .err error) : error = .abort .typeError := by
  rw [doApp_blockFromList_pure] at run
  cases found : blockFromListValue tag args with
  | none => simpa [found] using run.symm
  | some value => simp [found] at run

/-- The state-independent outcome of an external call, retaining exactly the
reference-store and FFI updates that the BVI dispatcher copies back. -/
noncomputable def ffiEffect {F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List Value) (refs : HolFiniteMapExact Nat (Ref Value)) (ffi : HolFfiState F) :
    SemanticPrimitivesHOL.Result (HolFiniteMapExact Nat (Ref Value) × HolFfiState F) BviSem.ExnOrRet :=
  match args with
  | [.refPtr _ configPtr, .refPtr _ ptr] =>
    match refs.lookup configPtr, refs.lookup ptr with
    | some (.byteArray true config), some (.byteArray false bytes) =>
      match callFFIHOL ffi (.extCall name) config bytes with
      | .ret ffi' updated => .val (refs.updateEq (ptr, .byteArray false updated), ffi')
      | .final outcome => .err (.abort (.ffiError outcome))
    | _, _ => .err (.abort .typeError)
  | _ => .err (.abort .typeError)

/-- External calls update only the shared reference and FFI fields. -/
theorem doApp_ffi_effect {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List Value) (state : BviSem.BviState C F) :
    BviSem.doApp (.ffi name) args state =
      match ffiEffect name args state.refs state.ffi with
      | .err error => .err error
      | .val (refs, ffi) => .val (unitValue, { state with refs := refs, ffi := ffi }) := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, ffiEffect]
  | cons a rest =>
    cases rest with
    | nil => cases a <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, ffiEffect]
    | cons b rest =>
      cases rest with
      | cons c cs => cases a <;> cases b <;>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, ffiEffect]
      | nil =>
        cases a <;> cases b <;>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, ffiEffect,
            BviSem.toBvl, BviSem.fromBvl]
        rename_i flag1 ptr1 flag2 ptr2
        cases first : state.refs.lookup ptr1 with
        | none => simp
        | some ref1 =>
          cases second : state.refs.lookup ptr2 with
          | none => simp
          | some ref2 =>
            cases ref1 <;> cases ref2 <;> try simp
            all_goals rename_i xflag config yflag bytes
            all_goals cases xflag <;> cases yflag <;> try simp
            all_goals cases outcome : callFFIHOL state.ffi (.extCall name) config bytes <;>
              simp

/-- Successful external calls preserve related states, including the updated
reference bytes and FFI state. -/
theorem stateRel_doApp_ffi {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List Value) (source sourceNext : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (value : Value) (related : stateRel source target)
    (run : BviSem.doApp (.ffi name) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.ffi name) args target = .val (value, targetNext) ∧
      stateRel sourceNext targetNext := by
  have refs := (stateRel_const source target related).1
  have ffi := (stateRel_const source target related).2.2.2
  rw [doApp_ffi_effect] at run ⊢
  rw [refs, ffi]
  cases effect : ffiEffect name args source.refs source.ffi with
  | err error => simp [effect] at run
  | val pair =>
    obtain ⟨newRefs, newFfi⟩ := pair
    simp [effect] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨{ target with refs := newRefs, ffi := newFfi }, by simp, ?_⟩
    exact stateRel_withFfi _ _ newFfi (stateRel_withRefs source target newRefs related)

/-- External-call errors, including final FFI outcomes, agree in related states. -/
theorem stateRel_doApp_ffi_error {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List Value) (source : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet) (related : stateRel source target)
    (run : BviSem.doApp (.ffi name) args source = .err error) :
    BviSem.doApp (.ffi name) args target = .err error := by
  have refs := (stateRel_const source target related).1
  have ffi := (stateRel_const source target related).2.2.2
  rw [doApp_ffi_effect] at run ⊢
  rw [refs, ffi]
  cases effect : ffiEffect name args source.refs source.ffi with
  | err e => simpa [effect] using run
  | val pair => cases pair; simp [effect] at run

/-- Reading a global slot depends only on the shared global pointer and
reference store. -/
theorem stateRel_doApp_global {C F : Type} (index : Nat) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (result : Value) (related : stateRel source target)
    (run : BviSem.doApp (.globOp (.global index)) args source = .val (result, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.globOp (.global index)) args target = .val (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  cases args with
  | cons value rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | nil =>
    have refs := (stateRel_const source target related).1
    have global := (stateRel_const source target related).2.2.1
    cases pointer : source.global with
    | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer] at run
    | some ptr =>
      cases found : source.refs.lookup ptr with
      | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found] at run
      | some entry =>
        cases entry with
        | valueArray values =>
          cases item : values[index]? with
          | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found, item] at run
          | some value =>
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found, item] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨target, by simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
              global, refs, pointer, found, item], related⟩
        | _ => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found] at run

/-- Writing a global slot applies the same reference-store update on both
sides of the state relation. -/
theorem stateRel_doApp_setGlobal {C F : Type} (index : Nat) (args : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (result : Value) (related : stateRel source target)
    (run : BviSem.doApp (.globOp (.setGlobal index)) args source = .val (result, sourceNext)) :
    ∃ targetNext, BviSem.doApp (.globOp (.setGlobal index)) args target = .val (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons value rest =>
    cases rest with
    | cons x xs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | nil =>
      have refs := (stateRel_const source target related).1
      have global := (stateRel_const source target related).2.2.1
      cases pointer : source.global with
      | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer] at run
      | some ptr =>
        cases found : source.refs.lookup ptr with
        | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found] at run
        | some entry =>
          cases entry with
          | valueArray values =>
            by_cases bound : index < values.length
            · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found, bound] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨{ target with refs := source.refs.updateEq (ptr, .valueArray (values.set index value)) }, ?_,
                by simpa [pointer] using (stateRel_withRefs source target
                  (source.refs.updateEq (ptr, .valueArray (values.set index value))) related)⟩
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, global, refs, pointer, found, bound]
            · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found, bound] at run
          | _ => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found] at run

/-- A global-slot write reports only a type error. -/
theorem doApp_setGlobal_error {C F : Type} (index : Nat) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.globOp (.setGlobal index)) args state = .err error) : error = .abort .typeError := by
  cases args with
  | nil => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
  | cons value rest =>
    cases rest with
    | cons x xs => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
    | nil =>
      cases pointer : state.global with
      | none => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer] using run.symm
      | some ptr =>
        cases found : state.refs.lookup ptr with
        | none => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found] using run.symm
        | some entry =>
          cases entry with
          | valueArray values =>
            by_cases bound : index < values.length
            · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found, bound] at run
            · simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found, bound] using run.symm
          | _ => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found] using run.symm

/-- A global-slot read reports only a type error. -/
theorem doApp_global_error {C F : Type} (index : Nat) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.globOp (.global index)) args state = .err error) : error = .abort .typeError := by
  cases args with
  | cons value rest => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
  | nil =>
    cases pointer : state.global with
    | none => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer] using run.symm
    | some ptr =>
      cases found : state.refs.lookup ptr with
      | none => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found] using run.symm
      | some entry =>
        cases entry with
        | valueArray values =>
          cases item : values[index]? with
          | none => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found, item] using run.symm
          | some value => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found, item] at run
        | _ => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, pointer, found] using run.symm

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

/-- Accumulator primitives can fail only with the source type error. -/
theorem doApp_toOp_error_type {C F : Type} (op : AssocOp) (args : List Value)
    (state : BviSem.BviState C F) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (toOp op) args state = .err error) : error = .abort .typeError := by
  rw [doApp_toOp_pure] at run
  cases found : accumulatorApply op args with
  | none => simpa [found] using run.symm
  | some value => simp [found] at run

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

/-- Appending a well-typed accumulator to call arguments establishes the
worker's environment relation. -/
theorem envRel_worker (op : AssocOp) (args : List Value) (value : Value)
    (notNoop : op ≠ .noop) (typed : valueMatchesType value (opType op)) :
    envRel (opType op) true args.length args (args ++ [value]) := by
  cases op with
  | plus =>
    obtain ⟨integer, rfl⟩ := typed.1 rfl
    simp [envRel, opType]
  | times =>
    obtain ⟨integer, rfl⟩ := typed.1 rfl
    simp [envRel, opType]
  | append =>
    obtain ⟨values, decode⟩ := typed.2 rfl
    simp [envRel, opType, decode]
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
