import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockCons
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateIf

/-! Block inspection primitives in the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.SemanticPrimitivesHOL

/-- Reserving closure tags does not identify distinct constructor tags. -/
theorem closTagShift_injective : Function.Injective closTagShift := by
  intro a b equal
  simp only [closTagShift] at equal
  split at equal <;> split at equal <;> omega

/-- Source block inspections that do not update the state. -/
inductive BlockInspect where
  | length
  | elemAt : Nat → BlockInspect
  | lengthEq : Nat → BlockInspect
  | tagEq : Nat → BlockInspect
  | tagLengthEq : Nat → Nat → BlockInspect
  deriving DecidableEq

/-- Corresponding closure-language primitive. -/
def BlockInspect.op : BlockInspect → ClosLang.Op
  | .length => .blockOp .lengthBlock
  | .elemAt index => .blockOp (.elemAt index)
  | .lengthEq n => .blockOp (.lenEq n)
  | .tagEq n => .blockOp (.tagEq n)
  | .tagLengthEq tag n => .blockOp (.tagLenEq tag n)

private theorem fieldsEnvRel {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {xs : List ClosSem.Value} {ys : List BvlSem.Value}
    (related : List.Forall₂ (vRel maxApp f refs code) xs ys) : envRel maxApp f refs code xs ys := by
  induction related with
  | nil => trivial
  | cons head tail ih => exact ⟨head, ih⟩

/-- A successful block inspection returns related values and leaves both
states unchanged. -/
theorem blockInspect_related {C F : Type} {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    (op : BlockInspect) (tag : Nat) (fields : List ClosSem.Value) (target : BvlSem.Value)
    (s : ClosSem.State C F) (t : BvlSem.State C F)
    (related : vRel maxApp f t.refs t.code (.block tag fields) target)
    (success : ∃ value next, ClosSem.doApp op.op [.block tag fields] s = .val (value, next)) :
    ∃ sourceValue targetValue,
      ClosSem.doApp op.op [.block tag fields] s = .val (sourceValue, s) ∧
      BvlSem.doApp (compileOp op.op) [target] t = .val (targetValue, t) ∧
      vRel maxApp f t.refs t.code sourceValue targetValue := by
  obtain ⟨targetFields, rfl, fieldsRel⟩ := vRel_block_inv related
  have lengths := fieldsRel.length_eq
  have tagEq : (closTagShift tag == closTagShift ·) = (tag == ·) := by
    funext other
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq] using (closTagShift_injective.eq_iff (a := tag) (b := other))
  cases op with
  | length =>
    refine ⟨.number fields.length, .number targetFields.length, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · simpa [lengths] using (vRel.number (Int.ofNat fields.length) :
        vRel maxApp f t.refs t.code (.number fields.length) (.number fields.length))
  | elemAt index =>
    obtain ⟨value, next, run⟩ := success
    cases found : fields[index]? with
    | none => simp [BlockInspect.op, ClosSem.doApp, ClosSem.applyBlock, found] at run
    | some field =>
      obtain ⟨targetField, targetFound, fieldRel⟩ := envRel_lookup (fieldsEnvRel fieldsRel) found
      refine ⟨field, targetField, ?_, ?_, fieldRel⟩
      · simp [BlockInspect.op, ClosSem.doApp, ClosSem.applyBlock, found]
      · simp [BlockInspect.op, compileOp, BvlSem.doApp, BvlSem.applyBlock, targetFound]
  | lengthEq n =>
    refine ⟨ClosSem.boolValue (fields.length == n), BvlSem.boolValue (targetFields.length == n), ?_, ?_, ?_⟩
    · rfl
    · rfl
    · simpa [lengths] using (vRel_bool (maxApp := maxApp) (f := f) (refs := t.refs) (code := t.code) (fields.length == n))
  | tagEq n =>
    refine ⟨ClosSem.boolValue (tag == n), BvlSem.boolValue (closTagShift tag == closTagShift n), ?_, ?_, ?_⟩
    · rfl
    · rfl
    · simpa [congrFun tagEq n] using (vRel_bool (maxApp := maxApp) (f := f) (refs := t.refs) (code := t.code) (tag == n))
  | tagLengthEq n len =>
    refine ⟨ClosSem.boolValue (tag == n && fields.length == len),
      BvlSem.boolValue (closTagShift tag == closTagShift n && targetFields.length == len), ?_, ?_, ?_⟩
    · rfl
    · rfl
    · simpa [lengths, congrFun tagEq n] using (vRel_bool (maxApp := maxApp) (f := f) (refs := t.refs) (code := t.code) (tag == n && fields.length == len))

/-- A successful inspection receives exactly one block. -/
theorem blockInspect_success_shape {C F : Type} (op : BlockInspect)
    (args : List ClosSem.Value) (s next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp op.op args s = .val (value, next)) :
    ∃ tag fields, args = [.block tag fields] := by
  cases op <;> cases args with
  | nil => simp [BlockInspect.op, ClosSem.doApp, ClosSem.applyBlock] at run
  | cons a rest =>
    cases rest with
    | nil =>
      cases a <;> simp_all [BlockInspect.op, ClosSem.doApp, ClosSem.applyBlock]
    | cons b rest => simp [BlockInspect.op, ClosSem.doApp, ClosSem.applyBlock] at run

/-- Successful inspection of related arguments preserves the value relation. -/
theorem blockInspect_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (op : BlockInspect) (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp op.op args s = .val (value, next)) :
    ∃ targetValue, BvlSem.doApp (compileOp op.op) targets t = .val (targetValue, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value targetValue := by
  obtain ⟨tag, fields, rfl⟩ := blockInspect_success_shape op args s next value run
  cases related with
  | cons head tail =>
    cases tail
    obtain ⟨sourceValue, targetValue, sourceRun, targetRun, valueRel⟩ :=
      blockInspect_related op tag fields _ s t head ⟨value, next, run⟩
    rw [sourceRun] at run
    cases run
    exact ⟨targetValue, targetRun, rfl, valueRel⟩

/-- Inspection failures are exactly type errors. -/
theorem blockInspect_error {C F : Type} (op : BlockInspect) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp op.op args s = .err error) : error = .abort .typeError := by
  cases op <;> cases args with
  | nil => simpa [BlockInspect.op, ClosSem.doApp, ClosSem.applyBlock] using run.symm
  | cons a rest =>
    cases rest with
    | nil => cases a <;> simp_all [BlockInspect.op, ClosSem.doApp, ClosSem.applyBlock] <;>
        split at run <;> simp_all
    | cons b rest => simpa [BlockInspect.op, ClosSem.doApp, ClosSem.applyBlock] using run.symm

/-- Evaluation of an inspection evaluates arguments before dispatch. -/
theorem evaluate_blockInspect {C F : Type} (trace : BackendCommon.Tra) (op : BlockInspect)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s : ClosSem.State C F) :
    ClosSem.evaluate [.op trace op.op args] env s =
      match ClosSem.evaluate args env s with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => match ClosSem.doApp op.op values.reverse next with
        | .err error => (.err error, next)
        | .val (value, last) => (.val [value], last) := by
  cases op <;> rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] <;>
    simp only [BlockInspect.op] <;> cases h : ClosSem.evaluate args env s with
  | mk result next => cases result <;> rfl

end Flapjack.Compiler.Backend.ClosToBvl
