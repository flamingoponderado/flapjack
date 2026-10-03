import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Misc.ShiftSeq

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.FFI
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Canonical imported state codec witness; representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Full native FFI case of the original three-conjunct existential theorem.
Register/bytearray read failures, final FFI and returning FFI all preserve
compileOracle, code and bitmaps, so the count is zero. No target evaluation,
poststate field fact, name restriction or byte-alignment premise is supplied.
The evaluator closure inherits reals_as_rational_cuts; this case does not assert
floating-point or numerical alignment correspondence. Parent assembly remains open. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_code_bitmaps"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCodeBitmapsFFI {width : Nat} [NeZero width] {C F : Type}
    (ffiIndex : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate
      (.ffi ffiIndex ptr len ptr2 len2 ret, source) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count source.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (source.compileOracle index).2.1)).foldl sptUnion source.code ∧
      post.bitmaps = source.bitmaps ++ ((List.range count).map
        (fun index => (source.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_ffi] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, by simp, by simp⟩

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.FFI
