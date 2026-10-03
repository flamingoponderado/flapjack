import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Seq

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

namespace CallReturnCase
/-- Imported canonical codec re-export; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end CallReturnCase

/-- Full Call SOME case: callee and continuation IHs are guarded by the
actual code lookup, clock and native intermediate execution. No arbitrary-state
IH or target/poststate field premise is supplied. Prefix composition retains
all three original conjuncts. The evaluator inherits reals_as_rational_cuts;
no numeric alignment/FP correspondence is asserted. Whole assembly is open. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_code_bitmaps"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCodeBitmapsCallReturn {width : Nat} [NeZero width] {C F : Type}
    (retH : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : ∀ (prog : HolProg width),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog →
      source.clock ≠ 0 →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) source)) = (res, out) →
      CodeBitmaps (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) out)
    (returnIH : ∀ (prog : HolProg width),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog →
      source.clock ≠ 0 → ∀ (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.result (.loc l1 l2)), middle) →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (retH, {middle with clock := min (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)).clock middle.clock}) = (res, out) →
      CodeBitmaps {middle with clock := min (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)).clock middle.clock} out)
    (exceptionIH : ∀ (prog h : HolProg width) (hl1 hl2 : Nat),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog →
      source.clock ≠ 0 → handler = some (h, hl1, hl2) →
      ∀ (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.exception (.loc hl1 hl2)), middle) →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (h, {middle with clock := min (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)).clock middle.clock}) = (res, out) →
      CodeBitmaps {middle with clock := min (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)).clock middle.clock} out)
    (execution : StackSemEvaluate.evaluate
      (.call (some (retH, link, l1, l2)) dest handler, source) = (result, post)) :
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
    split at execution
    · simp only [Prod.mk.injEq] at execution
      obtain ⟨-, equality⟩ := execution
      subst post
      exact ⟨0, rfl, by simp [StackSemStateOps.emptyEnv], by simp [StackSemStateOps.emptyEnv]⟩
    · rename_i clock
      rcases evaluated : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) source)) with ⟨res, middle⟩
      have fields := calleeIH prog lookup clock res middle evaluated
      have clamped : CodeBitmaps source {middle with clock := min (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)).clock middle.clock} := fields
      rw [evaluated] at execution
      simp only [StackSemControl.fixClock] at execution
      cases res with
      | none =>
        simp only [Prod.mk.injEq] at execution
        exact execution.2 ▸ clamped
      | some value =>
        cases value <;> dsimp only at execution
        all_goals first
          | (simp only [Prod.mk.injEq] at execution; exact execution.2 ▸ clamped)
          | skip
        case result x =>
          by_cases equal : x = .loc l1 l2
          · subst x
            simp only [ne_eq, not_true_eq_false, if_false] at execution
            exact clamped.trans (returnIH prog lookup clock middle evaluated result post execution)
          · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
            exact execution.2 ▸ clamped
        case exception x =>
          cases handler with
          | none =>
            dsimp only at execution
            simp only [Prod.mk.injEq] at execution
            exact execution.2 ▸ clamped
          | some triple =>
            obtain ⟨h, hl1, hl2⟩ := triple
            dsimp only at execution
            by_cases equal : x = .loc hl1 hl2
            · subst x
              simp only [ne_eq, not_true_eq_false, if_false] at execution
              exact clamped.trans (exceptionIH prog h hl1 hl2 lookup clock rfl middle evaluated result post execution)
            · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
              exact execution.2 ▸ clamped

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
