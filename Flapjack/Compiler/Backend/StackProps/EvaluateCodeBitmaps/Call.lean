import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.CallTail
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.CallReturn

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

namespace CallCase
/-- Imported canonical codec re-export; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end CallCase

/-- Full original Call constructor, assembled from its actual NONE/SOME
native cases. Induction hypotheses retain only actual ret/source-path guards;
no global arbitrary-state IH, target execution or poststate field premise.
All three original existential conjuncts remain literal CodeBitmaps.
The evaluator closure inherits reals_as_rational_cuts; no numerical alignment
or FP correspondence is asserted. Whole evaluator assembly remains open. The
`tailIH`, `calleeIH`, `returnIH` and `exceptionIH` are the original
`evaluate_ind` recursive hypotheses for the `none`/first-`some` and handler
branches, each guarded by the actual `ret` shape, code lookup, nonzero clock
and (for the continuation) the actual `decClock`/`min`-clamped intermediate
state; no hypothesis is taken at an arbitrary state. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_code_bitmaps"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCodeBitmapsCall {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (tailIH : ret = none → ∀ (prog : HolProg width),
      StackSemControl.findCode dest source.regs source.code = some prog →
      handler = none → source.clock ≠ 0 →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock source) = (res, out) →
      CodeBitmaps (StackSemStateOps.decClock source) out)
    (calleeIH : ∀ (retH : HolProg width) (link l1 l2 : Nat),
      ret = some (retH, link, l1, l2) → ∀ (prog : HolProg width),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog →
      source.clock ≠ 0 →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) source)) = (res, out) →
      CodeBitmaps (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) out)
    (returnIH : ∀ (retH : HolProg width) (link l1 l2 : Nat),
      ret = some (retH, link, l1, l2) → ∀ (prog : HolProg width),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog →
      source.clock ≠ 0 → ∀ (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.result (.loc l1 l2)), middle) →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (retH, {middle with clock := min (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)).clock middle.clock}) = (res, out) →
      CodeBitmaps {middle with clock := min (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)).clock middle.clock} out)
    (exceptionIH : ∀ (retH : HolProg width) (link l1 l2 : Nat),
      ret = some (retH, link, l1, l2) → ∀ (prog h : HolProg width) (hl1 hl2 : Nat),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog →
      source.clock ≠ 0 → handler = some (h, hl1, hl2) →
      ∀ (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.exception (.loc hl1 hl2)), middle) →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (h, {middle with clock := min (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)).clock middle.clock}) = (res, out) →
      CodeBitmaps {middle with clock := min (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)).clock middle.clock} out)
    (execution : StackSemEvaluate.evaluate (.call ret dest handler, source) = (result, post)) :
    CodeBitmaps source post := by
  cases ret with
  | none => exact evaluateCodeBitmapsCallTail dest handler source post result (tailIH rfl) execution
  | some triple =>
    obtain ⟨retH, link, l1, l2⟩ := triple
    exact evaluateCodeBitmapsCallReturn retH link l1 l2 dest handler source post result
      (calleeIH retH link l1 l2 rfl) (returnIH retH link l1 l2 rfl)
      (exceptionIH retH link l1 l2 rfl) execution

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
