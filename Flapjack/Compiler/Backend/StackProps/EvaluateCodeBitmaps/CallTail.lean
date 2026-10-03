import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Seq

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

namespace CallTailCase
/-- Imported canonical codec re-export; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end CallTailCase

/-- Genuine Call NONE case of the original theorem, with callee IH only at
actual decClock source after successful lookup, absent handler and nonzero
clock. fixClock changes clock only. The full evaluator closure inherits
reals_as_rational_cuts; no numerical alignment/FP equivalence is asserted.
Returning/exception Call branches and whole evaluator assembly remain open. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_code_bitmaps"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCodeBitmapsCallTail {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : ∀ (prog : HolProg width),
      StackSemControl.findCode dest source.regs source.code = some prog →
      handler = none → source.clock ≠ 0 →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock source) = (res, out) →
      CodeBitmaps (StackSemStateOps.decClock source) out)
    (execution : StackSemEvaluate.evaluate (.call none dest handler, source) = (result, post)) :
    CodeBitmaps source post := by
  classical
  rw [StackSemEvaluate.evaluate_call] at execution
  dsimp only at execution
  split at execution
  · simp only [Prod.mk.injEq] at execution
    obtain ⟨-, equality⟩ := execution
    subst post
    exact ⟨0, rfl, by simp, by simp⟩
  · rename_i prog lookup
    cases handler with
    | some handler =>
      dsimp only at execution
      simp only [Prod.mk.injEq] at execution
      obtain ⟨-, equality⟩ := execution
      subst post
      exact ⟨0, rfl, by simp, by simp⟩
    | none =>
      dsimp only at execution
      split at execution
      · simp only [Prod.mk.injEq] at execution
        obtain ⟨-, equality⟩ := execution
        subst post
        exact ⟨0, rfl, by simp [StackSemStateOps.emptyEnv], by simp [StackSemStateOps.emptyEnv]⟩
      · rename_i clock
        rcases evaluated : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock source) with ⟨res, out⟩
        have fields := calleeIH prog lookup rfl clock res out evaluated
        rw [evaluated] at execution
        simp only [StackSemControl.fixClock] at execution
        have clamped : CodeBitmaps source
            {out with clock := min (StackSemStateOps.decClock source).clock out.clock} := fields
        by_cases bad : StackSemControl.badFunReturn res = true
        · simp only [bad, if_true, Prod.mk.injEq] at execution
          exact execution.2 ▸ clamped
        · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
          exact execution.2 ▸ clamped

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
