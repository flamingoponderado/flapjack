import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Seq

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang

namespace LoopCase
/-- Imported canonical codec re-export; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end LoopCase

/-- Genuine original Loop case with body and strictly-smaller-clock re-entry
IHs only. Actual clamp/decrement derive clock descent; timeout emptyEnv and
exit preserve original fields, and re-entry composes the actual prefixes. -/
/- Source acceptance HOLD: this is currently an untagged Flapjack theorem
about the native evaluator, not an accepted exact HOL port. That evaluator
closure reaches byte primitives using riscvByteAlignHOL rather than the
reviewed total holByteAlign selector at low positive widths. Restore the tag
only after canonical routing repair, dependency source review and full gates.
The kernel-checked proof remains useful and its hypotheses are unchanged. -/
theorem evaluateCodeBitmapsLoop {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : ∀ (state out : StackSemStateFiniteExact width C F)
      (res : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (body, state) = (res, out) → CodeBitmaps state out)
    (loopIH : ∀ (state out : StackSemStateFiniteExact width C F)
      (res : Option (StackSemResult width)), state.clock < source.clock →
      StackSemEvaluate.evaluate (.loop body, state) = (res, out) → CodeBitmaps state out)
    (execution : StackSemEvaluate.evaluate (.loop body, source) = (result, post)) :
    CodeBitmaps source post := by
  rw [StackSemEvaluate.evaluate_loop] at execution
  rcases evaluated : StackSemEvaluate.evaluate (body, source) with ⟨res, middle⟩
  have bodyResult := bodyIH source middle res evaluated
  rw [evaluated] at execution
  have clamp : StackSemControl.fixClock source (res, middle) =
      (res, {middle with clock := min source.clock middle.clock}) := rfl
  rw [clamp] at execution
  dsimp only at execution
  split at execution
  · split at execution
    · simp only [Prod.mk.injEq] at execution
      obtain ⟨-, equality⟩ := execution
      subst post
      exact bodyResult
    · rename_i nonzero
      have decrease : (StackSemStateOps.decClock
          {middle with clock := min source.clock middle.clock}).clock < source.clock := by
        change min source.clock middle.clock - 1 < source.clock
        change min source.clock middle.clock ≠ 0 at nonzero
        have bound := Nat.min_le_left source.clock middle.clock
        omega
      have recursive := loopIH _ post result decrease execution
      have initial : CodeBitmaps source (StackSemStateOps.decClock
          {middle with clock := min source.clock middle.clock}) := bodyResult
      exact initial.trans recursive
  · simp only [Prod.mk.injEq] at execution
    obtain ⟨-, equality⟩ := execution
    subst post
    exact bodyResult

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
