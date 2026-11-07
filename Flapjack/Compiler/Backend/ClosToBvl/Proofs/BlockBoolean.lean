import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateIf
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IntegerRelation

/-! Boolean block primitives in the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- Boolean primitives, which preserve the state on success. -/
inductive BlockBoolean where
  | not
  | test : AstHOL.Test → BlockBoolean

/-- Source operator corresponding to a Boolean primitive. -/
def BlockBoolean.op : BlockBoolean → ClosLang.Op
  | .not => .blockOp .boolNot
  | .test testOp => .blockOp (.boolTest testOp)

/-- A successful Boolean primitive produces related values. -/
theorem blockBoolean_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (op : BlockBoolean) (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp op.op args s = .val (value, next)) :
    ∃ targetValue, BvlSem.doApp (compileOp op.op) targets t = .val (targetValue, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value targetValue := by
  cases op with
  | not =>
    cases args with
    | nil => simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock] at run
    | cons a rest =>
      cases rest with
      | nil =>
        cases related with
        | cons head tail =>
          cases tail
          cases decoded : ClosSem.asBool a with
          | none => simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock, decoded] at run
          | some b =>
            have targetDecoded := vRel_asBool head decoded
            simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock, decoded] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨BvlSem.boolValue (!b), ?_, rfl, vRel_bool (!b)⟩
            simp [BlockBoolean.op, compileOp, BvlSem.doApp, BvlSem.applyBlock, targetDecoded]
      | cons b rest => simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock] at run
  | test test =>
    cases args with
    | nil => simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock] at run
    | cons a rest =>
      cases rest with
      | nil => simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock] at run
      | cons b rest =>
        cases rest with
        | nil =>
          cases related with
          | cons first tail =>
            cases tail with
            | cons second tail =>
              cases tail
              cases firstBool : ClosSem.asBool a with
              | none => simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock, firstBool] at run
              | some x =>
                cases secondBool : ClosSem.asBool b with
                | none => simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock, firstBool, secondBool] at run
                | some y =>
                  have targetFirst := vRel_asBool first firstBool
                  have targetSecond := vRel_asBool second secondBool
                  simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock, firstBool, secondBool] at run
                  rcases run with ⟨rfl, rfl⟩
                  refine ⟨BvlSem.boolValue (x == y), ?_, rfl, vRel_bool (x == y)⟩
                  simp [BlockBoolean.op, compileOp, BvlSem.doApp, BvlSem.applyBlock, targetFirst, targetSecond]
        | cons c rest => simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock] at run

/-- A Boolean primitive failure is a type error. -/
theorem blockBoolean_error {C F : Type} (op : BlockBoolean) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp op.op args s = .err error) : error = .abort .typeError := by
  cases op <;> cases args with
  | nil => simpa [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock] using run.symm
  | cons a rest =>
    cases rest with
    | nil =>
      simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock] at run
      all_goals try (exact run.symm)
      all_goals repeat' (split at run <;> simp_all)
    | cons b rest =>
      cases rest with
      | nil =>
        simp [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock] at run
        all_goals try (exact run.symm)
        all_goals repeat' (split at run <;> simp_all)
      | cons c rest => simpa [BlockBoolean.op, ClosSem.doApp, ClosSem.applyBlock] using run.symm

/-- Evaluation executes the arguments before a Boolean block primitive. -/
theorem evaluate_blockBoolean {C F : Type} (trace : BackendCommon.Tra) (op : BlockBoolean)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s : ClosSem.State C F) :
    ClosSem.evaluate [.op trace op.op args] env s =
      match ClosSem.evaluate args env s with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => match ClosSem.doApp op.op values.reverse next with
        | .err error => (.err error, next)
        | .val (value, last) => (.val [value], last) := by
  cases op <;> rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] <;>
    simp only [BlockBoolean.op] <;> cases h : ClosSem.evaluate args env s with
  | mk result next => cases result <;> rfl

end Flapjack.Compiler.Backend.ClosToBvl
