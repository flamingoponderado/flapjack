import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpCalls
import Flapjack.Compiler.Backend.BvlInline.Proofs.Semantics

/-! Whole-program observations of the let-operation and handler pipeline. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem

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
  have related : mappedStateRel (letOpTransform splitSeq limit) source target :=
    letOp_initialStateRel splitSeq limit clock ffi program oracle compiler
  obtain ⟨targetFinal, targetRun, finalRel⟩ :=
    letOpSimulation_all splitSeq limit [.call 0 (some start) []] [] source
      run.1 run.2 target related (by simp [run]) safe
  have targetRun' : evaluate [.call 0 (some start) []] [] target = (run.1, targetFinal) := by
    simpa [letOp, letOpList, letOpOne] using targetRun
  have ffiEq : targetFinal.ffi = run.2.ffi := by
    simpa using congrArg (fun s : State C F => s.ffi) finalRel.1
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
