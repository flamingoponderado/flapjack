import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap
namespace Flapjack.WordToStackProofs.LoopHandler
/-- Genuine canonical imported source carrier roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Full original evaluate_cont_loop_handler (7724–7733), retaining the actual
source evaluation and continuation guard. Evaluator closure inherits
reals_as_rational_cuts; no independent real-analysis agreement is claimed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateContLoopHandler {width : Nat} [NeZero width] {C F : Type}
    (program : WordLangProgHOL (BitVec width))
    (source post : WordSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate program source = (result,post))
    (continues : wordSemContLoop result = true) : post.handler = source.handler := by
  have preserved := WordSemStackEq.evaluateStackSwap program source
  unfold WordSemStackEq.stackSwapPost at preserved
  rw [execution] at preserved
  cases result with
  | none => exact preserved.2.1
  | some result =>
    cases result <;> simp [wordSemContLoop] at continues
    next n => exact preserved.2.1
end Flapjack.WordToStackProofs.LoopHandler
