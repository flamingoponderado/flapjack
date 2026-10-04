import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
import Flapjack.Misc.Sptree.Subspt

namespace Flapjack.Compiler.Backend.StackProps.EvaluateMono
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Canonical imported state codec witness; representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Full original unconditional evaluator monotonicity theorem. The only
premise is actual source evaluation: errors, timeouts, final FFI and successful
results all preserve the bitmap prefix and every original code lookup.
The native evaluator closure inherits reals_as_rational_cuts (SOUNDNESS item 8);
this theorem does not assert numerical FP or full compiler correspondence. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateMono {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (program, source) = (result, post)) :
    source.bitmaps.IsPrefix post.bitmaps ∧ sptSubspt source.code post.code := by
  obtain ⟨count, -, code, bitmaps⟩ := EvaluateCodeBitmaps.evaluateCodeBitmaps program source result post execution
  constructor
  · exact ⟨_, bitmaps.symm⟩
  · rw [code]
    exact sptSubsptFoldlUnion _ _

end Flapjack.Compiler.Backend.StackProps.EvaluateMono
