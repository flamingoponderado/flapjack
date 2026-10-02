import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Seq

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

namespace IfCase
/-- Imported canonical codec re-export; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end IfCase

/-- Genuine original If case: actual execution and genuine branch IHs
only. All failed reads/comparisons retain the original fields with count zero. -/
/- Source acceptance HOLD: this is currently an untagged Flapjack theorem
about the native evaluator, not an accepted exact HOL port. That evaluator
closure reaches byte primitives using riscvByteAlignHOL rather than the
reviewed total holByteAlign selector at low positive widths. Restore the tag
only after canonical routing repair, dependency source review and full gates.
The kernel-checked proof remains useful and its hypotheses are unchanged. -/
theorem evaluateCodeBitmapsIf {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : HolRegImm width)
    (first second : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ∀ (state out : StackSemStateFiniteExact width C F)
      (res : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (first, state) = (res, out) → CodeBitmaps state out)
    (secondIH : ∀ (state out : StackSemStateFiniteExact width C F)
      (res : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (second, state) = (res, out) → CodeBitmaps state out)
    (execution : StackSemEvaluate.evaluate
      (.ite comparison register operand first second, source) = (result, post)) :
    CodeBitmaps source post := by
  rw [StackSemEvaluate.evaluate_ite] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution)
  all_goals first
    | exact firstIH source post result execution
    | exact secondIH source post result execution
    | exact ⟨0, rfl, by simp, by simp⟩

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
