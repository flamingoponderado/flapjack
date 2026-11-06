import Flapjack.Compiler.Backend.BvlInline.Proofs.MappedApply
import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpProduction
import Flapjack.Compiler.Backend.BvlHandle.Proofs.ConstantComposition

/-! Runtime state relation for the combined let-operation and handler pass. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- Source-shaped total version of the handler pipeline actually executed
after let-operation optimization. -/
def letOpTransform (splitSeq : Bool) (limit arity : Nat) (body : Bvl.Exp) : Bvl.Exp :=
  let optimized := letOpSing body
  if arity == 0 && splitSeq then
    BvlHandle.compileSeqsWith (fun limit e => BvlHandle.compileExpression limit 0 e) limit optimized none
  else BvlHandle.compileExpression limit arity optimized

/-- A successful production let-operation traversal followed by handler
compilation returns the source-shaped combined transformation. -/
theorem letOpTransform_production (fuel optFuel : Nat) (splitSeq : Bool) (limit arity : Nat)
    (body optimized : Bvl.Exp) (run : letOpFuel fuel body = some optimized) :
    BvlHandle.compileAnyFuel optFuel splitSeq limit arity optimized =
      some (letOpTransform splitSeq limit arity body) := by
  have equal := letOpFuel_eq fuel body optimized run
  have one : letOpOne body = letOpSing body := by simp [letOpSing, letOp, letOpList]
  rw [equal, one, BvlHandle.compileAnyFuel_eq_source]
  rfl

/-- Compiler callback induced by the combined transformation. -/
def letOpCompiler {C : Type} (splitSeq : Bool) (limit : Nat) (compiler : Compiler C) : Compiler C :=
  fun config program => compiler config (program.map fun (name, arity, body) =>
    (name, arity, letOpTransform splitSeq limit arity body))

/-- Oracle induced by the combined transformation. -/
def letOpOracle {C : Type} (splitSeq : Bool) (limit : Nat) (oracle : CompileOracle C) : CompileOracle C :=
  fun clock => ((oracle clock).1, (oracle clock).2.map fun (name, arity, body) =>
    (name, arity, letOpTransform splitSeq limit arity body))

/-- The initial states of the source and transformed programs satisfy the
generic code-mapping relation. -/
theorem letOp_initialStateRel {C F : Type} (splitSeq : Bool) (limit clock : Nat)
    (ffi : HolFfiState F) (code : Spt (Nat × Bvl.Exp))
    (oracle : CompileOracle C) (compiler : Compiler C) :
    mappedStateRel (letOpTransform splitSeq limit)
      (initialState ffi code oracle (letOpCompiler splitSeq limit compiler) clock)
      (initialState ffi (sptMap (fun (arity, body) => (arity, letOpTransform splitSeq limit arity body)) code)
        (letOpOracle splitSeq limit oracle) compiler clock) := by
  constructor <;> rfl

/-- Primitive applications, including dynamic installation, preserve the
combined pass's state relation. This specializes the generic mapped-state
simulation and remains untagged pending review of the complete pass. -/
theorem letOp_doApp {C F : Type} (splitSeq : Bool) (limit : Nat) (s t : State C F)
    (related : mappedStateRel (letOpTransform splitSeq limit) s t)
    (op : ClosLang.Op) (args : List Value) :
    match doApp op args s with
    | .err error => doApp op args t = .err error
    | .val (value, next) => ∃ targetNext, mappedStateRel (letOpTransform splitSeq limit) next targetNext ∧
        doApp op args t = .val (value, targetNext) :=
  mappedDoApp (letOpTransform splitSeq limit) s t related op args

end Flapjack.Compiler.Backend.BvlInline.Proofs
