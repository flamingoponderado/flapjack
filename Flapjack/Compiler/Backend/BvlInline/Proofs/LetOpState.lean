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

/-- Optimize one arity and body pair with the source let-operation pass. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "let_opt_def"]
def letOpt (splitSeq : Bool) (limit : Nat) (entry : Nat × Bvl.Exp) : Nat × Bvl.Exp :=
  (entry.1, letOpTransform splitSeq limit entry.1 entry.2)

/-- Optimize a body after the source singleton tick-removal pass. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "let_opt_remove_def"]
def letOptRemove (splitSeq : Bool) (limit : Nat) (entry : Nat × Bvl.Exp) : Nat × Bvl.Exp :=
  letOpt splitSeq limit (entry.1, removeTicksSing entry.2)

/-- Compiler callback induced by the combined transformation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "let_op_cc_def"]
def letOpCompiler {Name C D : Type} (splitSeq : Bool) (limit : Nat)
    (compiler : C → List (Name × Nat × Bvl.Exp) → D) : C → List (Name × Nat × Bvl.Exp) → D :=
  fun config program => compiler config (program.map fun (name, body) =>
    (name, letOpt splitSeq limit body))

/-- Oracle induced by the combined transformation. -/
def letOpOracle {I C : Type} (splitSeq : Bool) (limit : Nat)
    (oracle : I → C × List (Nat × Nat × Bvl.Exp)) : I → C × List (Nat × Nat × Bvl.Exp) :=
  fun clock => ((oracle clock).1, (oracle clock).2.map fun (name, body) =>
    (name, letOpt splitSeq limit body))

namespace LetStateCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end LetStateCarrier

/-- The source relation for let optimization and handler compilation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "let_state_rel_def" 1422
  (fmap_as_finite_support := [refs])]
def letStateRel {C F : Type} (splitSeq : Bool) (limit : Nat)
    (source target : Flapjack.Compiler.Backend.BvlSem.State C F) : Prop :=
  mappedStateRel (letOpTransform splitSeq limit) source target

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
