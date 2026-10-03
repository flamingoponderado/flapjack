import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Compiler.Backend.StackProps.AllocationConstants

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang

namespace StoreConstsCase
/-- Imported canonical carrier roundtrip; representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end StoreConstsCase

/-- StoreConsts case of the original theorem, with all three existential
conjuncts and only the actual evaluator equation as premise. The full primitive
preservation lemma covers failures as well as successful copies; count zero
therefore follows without a successful-guard or post-state assumption. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_code_bitmaps"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCodeBitmapsStoreConsts {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (stub : Option Nat)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate
      (.storeConsts first second stub, source) = (result, post)) :
    (∃ count,
      post.compileOracle = holShiftSeq count source.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (source.compileOracle index).2.1)).foldl sptUnion source.code ∧
      post.bitmaps = source.bitmaps ++ ((List.range count).map
        (fun index => (source.compileOracle index).2.2)).flatten) := by
  rw [StackSemEvaluate.evaluate_storeConsts] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution)
  all_goals first
    | exact ⟨0, rfl, by simp, by simp⟩
    | (obtain ⟨-, -, -, -, -, code, -, -, -, -, bitmap, -, -, -, -, oracle⟩ :=
        StackPropsAllocationConstants.storeConstSemConst first second source post result execution
       exact ⟨0, oracle, by simpa using code, by simpa using bitmap⟩)

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
