import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Seq
import Flapjack.Compiler.Backend.StackProps.InstructionConstants

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

namespace InstCase
/-- Imported canonical codec re-export; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end InstCase

/-- Genuine Inst case: actual evaluator equality only. The successful
primitive preserves all three fields by the full original inst_const theorem;
failure retains source state. No successful instruction premise is exposed. -/
/- Source acceptance HOLD: this is currently an untagged Flapjack theorem
about the native evaluator, not an accepted exact HOL port. That evaluator
closure reaches byte primitives using riscvByteAlignHOL rather than the
reviewed total holByteAlign selector at low positive widths. Restore the tag
only after canonical routing repair, dependency source review and full gates.
The kernel-checked proof remains useful and its hypotheses are unchanged. -/
theorem evaluateCodeBitmapsInst {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.inst instruction, source) = (result, post)) :
    CodeBitmaps source post := by
  rw [StackSemEvaluate.evaluate_inst] at execution
  split at execution
  · rename_i target primitive
    simp only [Prod.mk.injEq] at execution
    obtain ⟨-, equality⟩ := execution
    subst post
    obtain ⟨-, -, -, -, -, code, -, -, -, -, bitmap, -, oracle⟩ :=
      StackPropsInstructionConstants.instConst instruction source target primitive
    exact ⟨0, oracle, by simpa using code, by simpa using bitmap⟩
  · simp only [Prod.mk.injEq] at execution
    obtain ⟨-, equality⟩ := execution
    subst post
    exact ⟨0, rfl, by simp, by simp⟩

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
