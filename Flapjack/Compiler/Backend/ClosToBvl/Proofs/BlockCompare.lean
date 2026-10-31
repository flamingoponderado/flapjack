import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockInspect
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WordRelation

/-! Numeric constant and block bounds comparisons for closure-to-BVL. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- Block comparisons with integer or word operands. -/
inductive BlockCompare where
  | intEq : Int → BlockCompare
  | wordEq : BitVec 64 → BlockCompare
  | bounds : BlockCompare

/-- Closure operator represented by a comparison. -/
def BlockCompare.op : BlockCompare → ClosLang.Op
  | .intEq n => .blockOp (.equalConst (.int n))
  | .wordEq w => .blockOp (.equalConst (.w64 w))
  | .bounds => .blockOp .boundsCheckBlock

/-- Successful comparisons preserve related values and leave both states unchanged. -/
theorem blockCompare_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (op : BlockCompare) (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp op.op args s = .val (value, next)) :
    ∃ targetValue, BvlSem.doApp (compileOp op.op) targets t = .val (targetValue, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value targetValue := by
  cases op with
  | intEq n =>
    cases args with
    | nil => simp [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] at run
    | cons a rest =>
      cases rest with
      | nil =>
        cases a <;> simp_all [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock]
        case number i =>
          cases related with
          | cons head tail =>
            cases tail
            have eq := vRel_number_inv head
            subst_vars
            rcases run with ⟨rfl, rfl⟩
            exact ⟨_, rfl, vRel_bool _⟩
      | cons b rest => simp [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] at run
  | wordEq w =>
    cases args with
    | nil => simp [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] at run
    | cons a rest =>
      cases rest with
      | nil =>
        cases a <;> simp_all [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock]
        case word64 i =>
          cases related with
          | cons head tail =>
            cases tail
            have eq := vRel_word64_inv head
            subst_vars
            rcases run with ⟨rfl, rfl⟩
            exact ⟨_, rfl, vRel_bool _⟩
      | cons b rest => simp [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] at run
  | bounds =>
    cases args with
    | nil => simp [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] at run
    | cons a rest =>
      cases rest with
      | nil => simp [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] at run
      | cons b rest =>
        cases rest with
        | nil =>
          cases a <;> simp_all [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock]
          case block tag fields =>
            cases b <;> simp_all
            case number index =>
              cases related with
              | cons first tail =>
                cases tail with
                | cons second tail =>
                  cases tail
                  obtain ⟨targetFields, rfl, fieldsRel⟩ := vRel_block_inv first
                  have eq := vRel_number_inv second
                  subst_vars
                  have lengths := fieldsRel.length_eq
                  rcases run with ⟨rfl, rfl⟩
                  refine ⟨_, rfl, ?_⟩
                  simpa [lengths] using (vRel_bool (maxApp := s.maxApp) (f := f) (refs := t.refs) (code := t.code)
                      (decide (0 ≤ index ∧ index < Int.ofNat fields.length)))
        | cons c rest => simp [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] at run

/-- These comparisons fail only with a type error. -/
theorem blockCompare_error {C F : Type} (op : BlockCompare) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp op.op args s = .err error) : error = .abort .typeError := by
  cases op <;> cases args with
  | nil => simpa [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] using run.symm
  | cons a rest =>
    cases rest with
    | nil => cases a <;> simp_all [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock]
    | cons b rest =>
      cases rest with
      | nil => cases a <;> simp_all [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] <;>
          cases b <;> simp_all
      | cons c rest => simpa [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] using run.symm

/-- Comparison arguments are evaluated before the primitive is dispatched. -/
theorem evaluate_blockCompare {C F : Type} (trace : BackendCommon.Tra) (op : BlockCompare)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s : ClosSem.State C F) :
    ClosSem.evaluate [.op trace op.op args] env s =
      match ClosSem.evaluate args env s with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => match ClosSem.doApp op.op values.reverse next with
        | .err error => (.err error, next)
        | .val (value, last) => (.val [value], last) := by
  cases op <;> rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] <;>
    simp only [BlockCompare.op] <;> cases h : ClosSem.evaluate args env s with
  | mk result next => cases result <;> rfl

end Flapjack.Compiler.Backend.ClosToBvl
