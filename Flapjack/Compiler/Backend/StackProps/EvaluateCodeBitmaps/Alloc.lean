import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Seq
import Flapjack.Compiler.Backend.StackProps.AllocationConstants

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang

namespace AllocCase
/-- Imported canonical codec re-export; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end AllocCase

/-- Genuine original Alloc case; actual evaluator equality only, including
allocation/GC errors and every rejected dispatch. -/
/- Source acceptance HOLD: this is currently an untagged Flapjack theorem
about the native evaluator, not an accepted exact HOL port. That evaluator
closure reaches byte primitives using riscvByteAlignHOL rather than the
reviewed total holByteAlign selector at low positive widths. Restore the tag
only after canonical routing repair, dependency source review and full gates.
The kernel-checked proof remains useful and its hypotheses are unchanged. -/
theorem evaluateCodeBitmapsAlloc {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.alloc register, source) = (result, post)) :
    CodeBitmaps source post := by
  rw [StackSemEvaluate.evaluate_alloc] at execution
  split at execution
  · simp only [Prod.mk.injEq] at execution
    obtain ⟨-, equality⟩ := execution
    subst post
    exact ⟨0, rfl, by simp, by simp⟩
  · split at execution
    · rename_i word _
      obtain ⟨-, -, -, -, -, code, -, -, -, -, bitmap, -, -, -, oracle⟩ :=
        StackPropsAllocationConstants.allocConst word source post result execution
      exact ⟨0, oracle, by simpa using code, by simpa using bitmap⟩
    · simp only [Prod.mk.injEq] at execution
      obtain ⟨-, equality⟩ := execution
      subst post
      exact ⟨0, rfl, by simp, by simp⟩

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
