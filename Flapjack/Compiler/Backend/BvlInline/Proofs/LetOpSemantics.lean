module

public import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpCalls
public import Flapjack.Compiler.Backend.BvlInline.Proofs.Semantics

@[expose] public section


/-! Whole-program observations of the let-operation and handler pipeline. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL (Result)

namespace LetCallCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end LetCallCarrier

/-- The initial call is simulated with the same result, FFI state, and clock. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "let_evaluate_Call"
  (fmap_as_finite_support := [refs])]
theorem letEvaluateCall {C F : Type} (splitSeq : Bool) (limit start clock : Nat)
    (ffi : HolFfiState F) (program : Spt (Nat × Bvl.Exp))
    (oracle : CompileOracle C) (compiler : Compiler C)
    (result : Result (List Value) Value) (final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (premises : evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi program oracle (letOpCompiler splitSeq limit compiler) clock) = (result, final) ∧
      result ≠ .err (.abort .typeError)) :
    ∃ targetFinal : Flapjack.Compiler.Backend.BvlSem.State C F,
      evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi (sptMap (letOpt splitSeq limit) program)
          (letOpOracle splitSeq limit oracle) compiler clock) = (result, targetFinal) ∧
      targetFinal.ffi = final.ffi ∧ final.clock = targetFinal.clock := by
  obtain ⟨run, safe⟩ := premises
  let source := initialState ffi program oracle (letOpCompiler splitSeq limit compiler) clock
  let target := initialState ffi (sptMap (letOpt splitSeq limit) program)
    (letOpOracle splitSeq limit oracle) compiler clock
  have transformEq : (fun (arity, body) => (arity, letOpTransform splitSeq limit arity body)) =
      letOpt splitSeq limit := by
    funext entry
    obtain ⟨arity, body⟩ := entry
    rfl
  have related : letStateRel splitSeq limit source target := by
    simpa only [source, target, letStateRel, transformEq] using
      letOp_initialStateRel splitSeq limit clock ffi program oracle compiler
  obtain ⟨targetFinal, targetRun, finalRel⟩ :=
    evaluateLetOp [.call 0 (some start) []] [] source result target final splitSeq limit
      ⟨related, run, safe⟩
  have fields := finalRel.1
  refine ⟨targetFinal, ?_, ?_, ?_⟩
  · simpa [target, letOp, letOpList, letOpOne] using targetRun
  · simpa using congrArg (fun state : State C F => state.ffi) fields
  · simpa using (congrArg (fun state : State C F => state.clock) fields).symm

/-- At each safe clock, the mapped program has the same result and I/O
events as the source program. -/
theorem letOp_initialObservation {C F : Type} (splitSeq : Bool) (limit start clock : Nat)
    (ffi : HolFfiState F) (program : Spt (Nat × Bvl.Exp))
    (oracle : CompileOracle C) (compiler : Compiler C)
    (safe : (evaluate [.call 0 (some start) []] []
      (initialState ffi program oracle (letOpCompiler splitSeq limit compiler) clock)).1 ≠
        .err (.abort .typeError)) :
    initialObservation ffi
      (sptMap (fun (arity, body) => (arity, letOpTransform splitSeq limit arity body)) program)
      (letOpOracle splitSeq limit oracle) compiler start clock =
    initialObservation ffi program oracle (letOpCompiler splitSeq limit compiler) start clock := by
  let source := initialState ffi program oracle (letOpCompiler splitSeq limit compiler) clock
  let target := initialState ffi
    (sptMap (fun (arity, body) => (arity, letOpTransform splitSeq limit arity body)) program)
    (letOpOracle splitSeq limit oracle) compiler clock
  let run := evaluate [.call 0 (some start) []] [] source
  obtain ⟨targetFinal, targetRun, ffiEq, _⟩ :=
    letEvaluateCall splitSeq limit start clock ffi program oracle compiler run.1 run.2
      ⟨by simp [source, run, evaluateTuple], safe⟩
  have transformEq : (fun (arity, body) => (arity, letOpTransform splitSeq limit arity body)) =
      letOpt splitSeq limit := by
    funext entry
    obtain ⟨arity, body⟩ := entry
    rfl
  have targetRun' : evaluate [.call 0 (some start) []] [] target = (run.1, targetFinal) := by
    simpa only [target, transformEq, evaluateTuple] using targetRun
  simp [initialObservation, source, target, run, targetRun', ffiEq]

/-- The combined let-operation and handler transformation preserves the
complete behavior of any non-failing initial program, including divergent
I/O traces. Untagged pending review of the evaluator and semantic carriers. -/
theorem letOp_semantics {C F : Type} (splitSeq : Bool) (limit start : Nat)
    (ffi : HolFfiState F) (program : Spt (Nat × Bvl.Exp))
    (oracle : CompileOracle C) (compiler : Compiler C)
    (nonFail : BvlSem.semantics ffi program oracle (letOpCompiler splitSeq limit compiler) start ≠ .fail) :
    BvlSem.semantics ffi
      (sptMap (fun (arity, body) => (arity, letOpTransform splitSeq limit arity body)) program)
      (letOpOracle splitSeq limit oracle) compiler start =
    BvlSem.semantics ffi program oracle (letOpCompiler splitSeq limit compiler) start := by
  have safe := BvlSem.noTypeError_of_semantics_ne_fail ffi program oracle
    (letOpCompiler splitSeq limit compiler) start nonFail
  have observations : initialObservation ffi
      (sptMap (fun (arity, body) => (arity, letOpTransform splitSeq limit arity body)) program)
      (letOpOracle splitSeq limit oracle) compiler start =
      initialObservation ffi program oracle (letOpCompiler splitSeq limit compiler) start := by
    funext clock
    exact letOp_initialObservation splitSeq limit start clock ffi program oracle compiler (safe clock)
  simp only [semantics_eq_clockSemantics, observations]

end Flapjack.Compiler.Backend.BvlInline.Proofs
