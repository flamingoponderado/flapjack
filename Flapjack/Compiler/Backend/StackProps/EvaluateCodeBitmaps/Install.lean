import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Misc.ShiftSeq

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Canonical imported state codec witness; representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Genuine Install case of the full source theorem. No count, oracle shift,
code prefix or bitmap extension is assumed. All three original existential
conjuncts are retained over the full native evaluator state. Original GENLIST
is List.range followed by map; union order is left accumulator. Every failure
leaves these fields unchanged (count zero), successful installation advances
exactly once (count one). This is one case, not the assembled theorem. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_code_bitmaps"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCodeBitmapsInstall {width : Nat} [NeZero width] {C F : Type}
    (codeBuffer codeLength dataBuffer dataLength returnAddress : Nat)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate
      (.install codeBuffer codeLength dataBuffer dataLength returnAddress, source) =
        (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count source.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (source.compileOracle index).2.1)).foldl sptUnion source.code ∧
      post.bitmaps = source.bitmaps ++ ((List.range count).map
        (fun index => (source.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_install] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals first
    | exact ⟨0, rfl, by simp, by simp⟩
    | (refine ⟨1, rfl, ?_, ?_⟩ <;> simp_all)

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
