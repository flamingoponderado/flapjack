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

/-- The BVI global allocation primitive always reports a type error. -/
theorem doApp_allocGlobal {C F : Type} (args : List Value) (state : BviSem.BviState C F) :
    BviSem.doApp (.globOp .allocGlobal) args state = .err (.abort .typeError) := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux]

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
