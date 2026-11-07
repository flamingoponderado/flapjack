import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockInspect
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WordRelation

/-! Constant and block bounds comparisons for closure-to-BVL. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

/-- Block comparisons with integer, word, or byte-vector operands. -/
inductive BlockCompare where
  | intEq : Int → BlockCompare
  | wordEq : BitVec 64 → BlockCompare
  | stringEq : MlString → BlockCompare
  | bounds : BlockCompare

/-- Closure operator represented by a comparison. -/
def BlockCompare.op : BlockCompare → ClosLang.Op
  | .intEq n => .blockOp (.equalConst (.int n))
  | .wordEq w => .blockOp (.equalConst (.w64 w))
  | .stringEq text => .blockOp (.equalConst (.str text))
  | .bounds => .blockOp .boundsCheckBlock

/-- A related byte vector points to the matching frozen target array. -/
theorem vRel_byteVector_inv {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {bytes : List (BitVec 8)} {target : BvlSem.Value}
    (related : vRel maxApp f refs code (.byteVector bytes) target) :
    ∃ ptr, target = .refPtr true ptr ∧ refs.lookup ptr = some (.byteArray true bytes) := by
  cases related with
  | byteVector found _ => exact ⟨_, rfl, found⟩
  | closure _ closure => cases closure
  | partialClosure _ _ _ _ _ added _ closure => cases closure <;> simp [addArgs] at added

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
  | stringEq text =>
    cases args with
    | nil => simp [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock] at run
    | cons a rest =>
      cases rest with
      | nil =>
        cases a <;> simp_all [BlockCompare.op, ClosSem.doApp, ClosSem.applyBlock]
        case byteVector bytes =>
          cases related with
          | cons head tail =>
            cases tail
            obtain ⟨ptr, rfl, found⟩ := vRel_byteVector_inv head
            rcases run with ⟨rfl, rfl⟩
            refine ⟨_, ?_, vRel_bool _⟩
            simp [compileOp, BvlSem.doApp, BvlSem.applyBlock, found]
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
