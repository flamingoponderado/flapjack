import Flapjack.Pancake.Semantics.LoopSemStateExact.ProductionEvalHook

/-!
# Production/exact Loop Op and Shift expression cases

HOL `loopSem$eval_def` (`cakeml/pancake/semantics/loopSemScript.sml:79-86`)
first evaluates all `Op` operands with `the_words` and then applies
`word_op`; `Shift` requires two word results and passes the second word's
`w2n` to `word_sh`. The candidate production `loopMachineEvalHook` uses the
same word operations, but its expression children are in `LoopExp` and its
results are `LoopValue`; the lemmas below combine genuine child-evaluation
agreement hypotheses across `holLoopExpToExecutable`. These are
Flapjack-specific cross-carrier bridges, not standalone HOL declarations, and
intentionally have no `@[hol]` tags. They do not establish a production caller
or a whole-evaluator theorem.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

private theorem loopValueToWordLocW_loopValueOfWordLocW {width : Nat}
    [NeZero width] (value : WordLocW width) :
    loopValueToWordLocW (loopValueOfWordLocW value) = value := by
  cases value <;> rfl

private theorem loopMachineEvalHook_toWordLocW_of_agreement {width : Nat}
    [NeZero width] {F : Type} (machine : LoopMachineState (BitVec width) F)
    (state : LoopSemStateFiniteExact width F) (expression : HolLoopExp width)
    (hAgreement : loopMachineEvalHook machine
        (holLoopExpToExecutable expression) =
      (LoopSemStateFiniteExact.eval state expression).map loopValueOfWordLocW) :
    (loopMachineEvalHook machine (holLoopExpToExecutable expression)).map
        loopValueToWordLocW = LoopSemStateFiniteExact.eval state expression := by
  rw [hAgreement]
  cases LoopSemStateFiniteExact.eval state expression with
  | none => rfl
  | some value => simp [loopValueToWordLocW_loopValueOfWordLocW]

/-- The candidate production `Op` hook agrees with exact `eval_def` when each
    operand is related by its recursive evaluation hypothesis. The `prodRel`
    premise is included as the evaluator-case context; once the child equations
    are supplied, this operation-only clause needs no additional state fields.
    `the_words` failure (missing or non-word operands) and unsupported
    `word_op` cases are preserved by the shared exact `theWords` and
    `wordOpHOL` definitions. -/
theorem loopMachineEvalHook_op_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (_hrel : state.prodRel machine) (operator : BinOp)
    (expressions : List (HolLoopExp width))
    (ih : ∀ expression, expression ∈ expressions →
      loopMachineEvalHook machine (holLoopExpToExecutable expression) =
        (LoopSemStateFiniteExact.eval state expression).map loopValueOfWordLocW) :
    loopMachineEvalHook machine
        (holLoopExpToExecutable (.op operator expressions)) =
      (LoopSemStateFiniteExact.eval state (.op operator expressions)).map
        loopValueOfWordLocW := by
  have hvalues :
      (expressions.map holLoopExpToExecutable).attach.map (fun item =>
        (loopMachineEvalHook machine item.val).map loopValueToWordLocW) =
      expressions.attach.map (fun item => LoopSemStateFiniteExact.eval state item.val) := by
    calc
      _ = expressions.attach.map (fun item =>
          (loopMachineEvalHook machine (holLoopExpToExecutable item.val)).map
            loopValueToWordLocW) := by
        rw [List.attach_map]
        simp only [List.map_map, Function.comp_def]
      _ = expressions.attach.map (fun item => LoopSemStateFiniteExact.eval state item.val) := by
        apply List.map_congr_left
        intro item hin
        exact loopMachineEvalHook_toWordLocW_of_agreement machine state item.val
          (ih item.val item.property)
  simp only [loopMachineEvalHook, holLoopExpToExecutable,
    LoopSemStateFiniteExact.eval]
  rw [hvalues]
  cases hwords : theWords
      (expressions.attach.map fun item => LoopSemStateFiniteExact.eval state item.val) with
  | none => simp
  | some words =>
      cases hop : wordOpHOL operator words <;>
        simp [hop, loopValueOfWordLocW]

/-- The candidate production `Shift` hook agrees with exact `eval_def` when
    the left and right child expressions satisfy their recursive evaluation
    hypotheses. A missing or non-word child yields `none` on both sides; for
    two words, both pass the right word's `toNat` to `wordShiftHOL`, including
    its width-indexed oversized-shift failure branch. -/
theorem loopMachineEvalHook_shift_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (_hrel : state.prodRel machine) (operator : Shift)
    (left right : HolLoopExp width)
    (ihLeft : loopMachineEvalHook machine (holLoopExpToExecutable left) =
      (LoopSemStateFiniteExact.eval state left).map loopValueOfWordLocW)
    (ihRight : loopMachineEvalHook machine (holLoopExpToExecutable right) =
      (LoopSemStateFiniteExact.eval state right).map loopValueOfWordLocW) :
    loopMachineEvalHook machine
        (holLoopExpToExecutable (.shift operator left right)) =
      (LoopSemStateFiniteExact.eval state (.shift operator left right)).map
        loopValueOfWordLocW := by
  cases hleft : LoopSemStateFiniteExact.eval state left with
  | none => simp [loopMachineEvalHook, holLoopExpToExecutable,
      LoopSemStateFiniteExact.eval, ihLeft, hleft]
  | some leftValue =>
      cases hright : LoopSemStateFiniteExact.eval state right with
      | none => simp [loopMachineEvalHook, holLoopExpToExecutable,
          LoopSemStateFiniteExact.eval, ihLeft, ihRight, hleft, hright]
      | some rightValue =>
          cases leftValue with
          | word leftWord =>
              cases rightValue with
              | word rightWord =>
                  cases hshift : wordShiftHOL operator leftWord rightWord.toNat <;>
                    simp [loopMachineEvalHook, holLoopExpToExecutable,
                      LoopSemStateFiniteExact.eval, ihLeft, ihRight, hleft,
                      hright, hshift, loopValueOfWordLocW]
              | loc identifier offset =>
                  simp [loopMachineEvalHook, holLoopExpToExecutable,
                    LoopSemStateFiniteExact.eval, ihLeft, ihRight, hleft,
                    hright, loopValueOfWordLocW]
          | loc identifier offset =>
              cases rightValue <;>
                simp [loopMachineEvalHook, holLoopExpToExecutable,
                  LoopSemStateFiniteExact.eval, ihLeft, ihRight, hleft,
                  hright, loopValueOfWordLocW]

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack
