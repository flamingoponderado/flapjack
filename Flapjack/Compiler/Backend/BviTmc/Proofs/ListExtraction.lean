import Flapjack.Compiler.Backend.BviTmc.Proofs.CallExtraction
import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractionWellFormed

/-! Multi-argument TMC extraction simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.ListExtraction
open BviTmc BviSem BvlSem

/-- Flapjack infrastructure: constructor evaluation after a successful first argument. -/
private theorem evaluate_cons_constructor {C F : Type} (tag : Nat) (x : Bvi.Exp)
    (xs : List Bvi.Exp) (env : List Value) (state next : BviState C F) (value : Value)
    (headRun : evaluate [x] env state = (.val [value], next)) :
    evaluate [.op (.blockOp (.cons tag)) (x :: xs)] env state =
      match evaluate xs env next with
      | (.err error, last) => (.err error, last)
      | (.val values, last) => (.val [.block tag (values.reverse ++ [value])], last) := by
  have listRun : evaluate (x :: xs) env state =
      match evaluate xs env next with
      | (.err error, last) => (.err error, last)
      | (.val values, last) => (.val (value :: values), last) := by
    change evaluateTuple (x :: xs, env, state) = _
    rw [evaluateCons]
    simp only [BviSem.evaluateTuple, headRun]
    dsimp only [Flapjack.holHd]
    cases evaluate xs env next with
    | mk result last => cases result <;> rfl
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, listRun]
  cases evaluate xs env next with
  | mk result last => cases result <;> simp [BviTailrec.doApp_blockCons]

/-- Flapjack infrastructure for the source list induction when extraction
finds its recursive call in the tail. The remaining list branch and the
assembling HOL theorem remain to be proved. -/
theorem evaluate_tail_call_case {C F : Type}
    (n loc tag : Nat) (x y : Bvi.Exp) (ys : List Bvi.Exp)
    (tailBs : List Bvi.Exp) (tailCb : CallBlock)
    (tailExtract : extractListSource n loc tag (y :: ys) = some (tailBs, .inr tailCb))
    (ih : ∀ (env : List Value) (state final : BviState C F) (result : BviResult)
      (bs : List Bvi.Exp) (cb : CallBlock),
      extractListSource n loc tag (y :: ys) = some (bs, .inr cb) →
      evaluate [.op (.blockOp (.cons tag)) (y :: ys)] env state = (result, final) →
      n ≤ env.length →
      ∃ argResult next, evaluate bs env state = (argResult, next) ∧
        (∀ values, argResult = .val values →
          evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
          ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
        (∀ error, argResult = .err error → (argResult, next) = (result, final)))
    (env : List Value) (state final : BviState C F) (result : BviResult)
    (bs : List Bvi.Exp) (cb : CallBlock)
    (extracted : extractListSource n loc tag (x :: y :: ys) = some (bs, .inr cb))
    (run : evaluate [.op (.blockOp (.cons tag)) (x :: y :: ys)] env state = (result, final))
    (bound : n ≤ env.length) :
    ∃ argResult next, evaluate bs env state = (argResult, next) ∧
      (∀ values, argResult = .val values →
        evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
        ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
      (∀ error, argResult = .err error → (argResult, next) = (result, final)) := by
  obtain ⟨_, left, child, right, rfl⟩ := extractList_wf_inr n loc tag (y :: ys) tailBs tailCb tailExtract
  simp [extractListSource, tailExtract, shiftBlock] at extracted
  obtain ⟨rfl, rfl⟩ := extracted.symm
  cases headRun : evaluate [x] env state with
  | mk headResult headState =>
    cases headResult with
    | err error =>
      have bindingsRun : evaluate (x :: tailBs) env state = (.err error, headState) := by
        change evaluateTuple (x :: tailBs, env, state) = _
        rw [evaluateCons]
        simp [BviSem.evaluateTuple, headRun]
      have original : evaluate [.op (.blockOp (.cons tag)) (x :: y :: ys)] env state =
          (.err error, headState) := by
        have listError : evaluate (x :: y :: ys) env state = (.err error, headState) := by
          change evaluateTuple (x :: y :: ys, env, state) = _
          rw [evaluateCons]
          simp [BviSem.evaluateTuple, headRun]
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, listError]
      refine ⟨.err error, headState, bindingsRun, ?_, ?_⟩
      · intro values impossible; cases impossible
      · intro other same; cases same; exact original.symm.trans run
    | val headValues =>
      obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton x env state headState headValues headRun
      cases tailRun : evaluate (y :: ys) env headState with
      | mk tailResult tailState =>
        cases tailResult with
        | err error =>
          have tailOp : evaluate [.op (.blockOp (.cons tag)) (y :: ys)] env headState =
              (.err error, tailState) := by
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, tailRun]
          obtain ⟨argResult, next, argsRun, success, failure⟩ :=
            ih env headState tailState (.err error) tailBs _ tailExtract tailOp bound
          have original : (SemanticPrimitivesHOL.Result.err error, tailState) = (result, final) := by
            rw [evaluate_cons_constructor tag x (y :: ys) env state headState value headRun, tailRun] at run
            exact run
          have bindingsRun : evaluate (x :: tailBs) env state =
              match argResult with
              | .err e => (.err e, next)
              | .val values => (.val (value :: values), next) := by
            change evaluateTuple (x :: tailBs, env, state) = _
            rw [evaluateCons]
            simp only [BviSem.evaluateTuple, headRun, argsRun]
            cases argResult <;> rfl
          cases argResult with
          | err argError =>
            have same := failure argError rfl
            refine ⟨.err argError, next, bindingsRun, ?_, ?_⟩
            · intro values impossible; cases impossible
            · intro other eq; cases eq; exact same.trans original
          | val values =>
            refine ⟨.val (value :: values), next, bindingsRun, ?_, ?_⟩
            · intro actual eq; cases eq
              obtain ⟨frameRun, extended⟩ := success values rfl
              constructor
              · exact (evaluate_prefixed_frame_error loc tag left right child value values next tailState error frameRun).trans original
              · intro extras
                have shifted := evaluate_prefixed_frame_error loc tag left right child value (values ++ extras) next
                  tailState error (extended extras)
                simpa [List.cons_append] using shifted.trans original
            · intro error impossible; cases impossible
        | val values =>
          have tailOp : evaluate [.op (.blockOp (.cons tag)) (y :: ys)] env headState =
              (.val [.block tag values.reverse], tailState) := by
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, tailRun]
            simp [BviTailrec.doApp_blockCons]
          obtain ⟨argResult, next, argsRun, success, failure⟩ :=
            ih env headState tailState (.val [.block tag values.reverse]) tailBs _ tailExtract tailOp bound
          have original : (SemanticPrimitivesHOL.Result.val [.block tag (values.reverse ++ [value])], tailState) =
              (result, final) := by
            rw [evaluate_cons_constructor tag x (y :: ys) env state headState value headRun, tailRun] at run
            exact run
          have bindingsRun : evaluate (x :: tailBs) env state =
              match argResult with
              | .err e => (.err e, next)
              | .val values => (.val (value :: values), next) := by
            change evaluateTuple (x :: tailBs, env, state) = _
            rw [evaluateCons]
            simp only [BviSem.evaluateTuple, headRun, argsRun]
            cases argResult <;> rfl
          cases argResult with
          | err argError => have impossible := failure argError rfl; cases impossible
          | val boundValues =>
            refine ⟨.val (value :: boundValues), next, bindingsRun, ?_, ?_⟩
            · intro actual eq; cases eq
              obtain ⟨frameRun, extended⟩ := success boundValues rfl
              obtain ⟨fields, equal, prefixed⟩ :=
                evaluate_prefixed_frame_success loc tag left right child value boundValues next tailState _ frameRun
              cases equal
              constructor
              · exact prefixed.trans original
              · intro extras
                obtain ⟨fields, equal, prefixed⟩ := evaluate_prefixed_frame_success loc tag left right child value
                  (boundValues ++ extras) next tailState _ (extended extras)
                cases equal
                simpa [List.cons_append] using prefixed.trans original
            · intro error impossible; cases impossible

end Flapjack.Compiler.Backend.BviTmc.ListExtraction
