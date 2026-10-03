import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Seq

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

namespace RawCallCase
/-- Imported canonical codec re-export; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end RawCallCase

/-- Full RawCall case of the original theorem, with a body IH only at the
actual source-path recursive call. Failed lookup, non-Seq code and timeout
preserve the tracked fields. The native evaluator closure inherits
reals_as_rational_cuts; no numeric alignment or floating-point correspondence
is asserted. This is a case, not the full evaluator assembly. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_code_bitmaps"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCodeBitmapsRawCall {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : ∀ (prog first body : HolProg width),
      sptLookup dest source.code = some prog →
      StackSemControl.destSeq prog = some (first, body) → source.clock ≠ 0 →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (body, StackSemStateOps.decClock source) = (res, out) →
      CodeBitmaps (StackSemStateOps.decClock source) out)
    (execution : StackSemEvaluate.evaluate (.rawCall dest, source) = (result, post)) :
    CodeBitmaps source post := by
  classical
  rw [StackSemEvaluate.evaluate_rawCall] at execution
  split at execution
  · simp only [Prod.mk.injEq] at execution
    obtain ⟨-, equality⟩ := execution
    subst post
    exact ⟨0, rfl, by simp, by simp⟩
  · split at execution
    · split at execution
      · simp only [Prod.mk.injEq] at execution
        obtain ⟨-, equality⟩ := execution
        subst post
        exact ⟨0, rfl, by simp [StackSemStateOps.emptyEnv], by simp [StackSemStateOps.emptyEnv]⟩
      · rename_i prog lookup pair first body destruct clock
        rcases evaluated : StackSemEvaluate.evaluate (body, StackSemStateOps.decClock source) with ⟨res, out⟩
        have fields := bodyIH prog first body lookup destruct clock res out evaluated
        rw [evaluated] at execution
        dsimp only at execution
        split at execution <;> simp only [Prod.mk.injEq] at execution <;>
          obtain ⟨-, equality⟩ := execution <;> subst post <;> exact fields
    · simp only [Prod.mk.injEq] at execution
      obtain ⟨-, equality⟩ := execution
      subst post
      exact ⟨0, rfl, by simp, by simp⟩

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
