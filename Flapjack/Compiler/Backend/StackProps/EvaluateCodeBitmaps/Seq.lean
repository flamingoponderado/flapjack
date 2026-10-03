import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Flapjack infrastructure naming the three literal original conjuncts;
not a separate HOL declaration. -/
def CodeBitmaps {width : Nat} [NeZero width] {C F : Type}
    (source post : StackSemStateFiniteExact width C F) : Prop :=
  ∃ count,
    post.compileOracle = holShiftSeq count source.compileOracle ∧
    post.code = ((List.range count).map
      (fun index => sptFromAList (source.compileOracle index).2.1)).foldl sptUnion source.code ∧
    post.bitmaps = source.bitmaps ++ ((List.range count).map
      (fun index => (source.compileOracle index).2.2)).flatten

/-- Prefix composition infrastructure: count addition follows actual oracle
shift, original left fold order and bitmap append; no prefix premise. -/
theorem CodeBitmaps.trans {width : Nat} [NeZero width] {C F : Type}
    {source middle post : StackSemStateFiniteExact width C F}
    (first : CodeBitmaps source middle) (second : CodeBitmaps middle post) :
    CodeBitmaps source post := by
  obtain ⟨a, oracleA, codeA, bitmapA⟩ := first
  obtain ⟨b, oracleB, codeB, bitmapB⟩ := second
  refine ⟨a + b, ?_, ?_, ?_⟩
  · rw [oracleB, oracleA]
    funext index
    simp [holShiftSeq, Nat.add_comm, Nat.add_left_comm]
  · rw [codeB, oracleA, codeA]
    simp [List.range_add, List.map_append, List.map_map, List.foldl_append,
      holShiftSeq, Function.comp_def, Nat.add_comm]
  · rw [bitmapB, oracleA, bitmapA]
    simp [List.range_add, List.map_append, List.map_map, List.flatten_append,
      holShiftSeq, Function.comp_def, Nat.add_comm, List.append_assoc]

namespace SeqCase
/-- Imported canonical codec re-export; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end SeqCase

/-- Genuine original Seq case: actual source execution plus only genuine
subprogram induction hypotheses. CodeBitmaps unfolds to the three literal
original existential conjuncts; no successful-result or clock premise.
The native evaluator closure retains inherited reals_as_rational_cuts; this
case asserts no numeric alignment or floating-point correspondence. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_code_bitmaps"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCodeBitmapsSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ∀ (res : Option (StackSemResult width))
      (out : StackSemStateFiniteExact width C F), StackSemEvaluate.evaluate (first, source) = (res, out) →
      CodeBitmaps source out)
    (secondIH : ∀ (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (first, source) = (none, middle) →
      ∀ (res : Option (StackSemResult width)) (out : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (second, {middle with clock := min source.clock middle.clock}) = (res, out) →
      CodeBitmaps {middle with clock := min source.clock middle.clock} out)
    (execution : StackSemEvaluate.evaluate (.seq first second, source) = (result, post)) :
    CodeBitmaps source post := by
  rw [StackSemEvaluate.evaluate_seq] at execution
  rcases evaluated : StackSemEvaluate.evaluate (first, source) with ⟨res, middle⟩
  have firstResult := firstIH res middle evaluated
  rw [evaluated] at execution
  have clamp : StackSemControl.fixClock source (res, middle) =
      (res, {middle with clock := min source.clock middle.clock}) := rfl
  rw [clamp] at execution
  have clamped : CodeBitmaps source {middle with clock := min source.clock middle.clock} := firstResult
  cases res with
  | none => exact clamped.trans (secondIH middle evaluated _ _ execution)
  | some value =>
    simp only [Prod.mk.injEq] at execution
    obtain ⟨-, equality⟩ := execution
    subst post
    exact clamped

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
