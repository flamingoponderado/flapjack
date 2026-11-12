module

public import Flapjack.Compiler.Backend.BvlInline.Proofs.MappedApply
public import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpProduction
public import Flapjack.Compiler.Backend.BvlHandle.SourceCompile

@[expose] public section

/-! Runtime state relation for the combined let-operation and handler pass. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- Source-shaped total version of the handler pipeline actually executed
after let-operation optimization. -/
def letOpTransform (splitSeq : Bool) (limit arity : Nat) (body : Bvl.Exp) : Bvl.Exp :=
  BvlHandle.compileAny splitSeq limit arity (letOpSing body)

/-- Compiler callback induced by the combined transformation. -/
def letOpCompiler {C D : Type} (splitSeq : Bool) (limit : Nat)
    (compiler : C → List (Nat × Nat × Bvl.Exp) → D) : C → List (Nat × Nat × Bvl.Exp) → D :=
  fun config program => compiler config (program.map fun (name, arity, body) =>
    (name, arity, letOpTransform splitSeq limit arity body))

/-- Oracle induced by the combined transformation. -/
def letOpOracle {I C : Type} (splitSeq : Bool) (limit : Nat)
    (oracle : I → C × List (Nat × Nat × Bvl.Exp)) : I → C × List (Nat × Nat × Bvl.Exp) :=
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
