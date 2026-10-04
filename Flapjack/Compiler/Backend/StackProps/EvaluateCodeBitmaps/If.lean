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
only. All failed reads/comparisons retain the original fields with count zero.
The native evaluator closure inherits reals_as_rational_cuts; this case makes
no numeric alignment or floating-point correspondence claim. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsIf {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : HolRegImm width)
    (first second : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ∀ (x y : WordLocW width),
      StackSemStateOps.getVar register source = some x →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y →
      wordSemWordCmp comparison x y = some true →
      ∀ (out : StackSemStateFiniteExact width C F) (res : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (first, source) = (res, out) → CodeBitmaps source out)
    (secondIH : ∀ (x y : WordLocW width),
      StackSemStateOps.getVar register source = some x →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y →
      wordSemWordCmp comparison x y = some false →
      ∀ (out : StackSemStateFiniteExact width C F) (res : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (second, source) = (res, out) → CodeBitmaps source out)
    (execution : StackSemEvaluate.evaluate
      (.ite comparison register operand first second, source) = (result, post)) :
    CodeBitmaps source post := by
  rw [StackSemEvaluate.evaluate_ite] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution)
  all_goals first
    | exact firstIH _ _ (by assumption) (by assumption) (by assumption) post result execution
    | exact secondIH _ _ (by assumption) (by assumption) (by assumption) post result execution
    | exact ⟨0, rfl, by simp, by simp⟩

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
