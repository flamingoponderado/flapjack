import Flapjack.Compiler.Backend.BviTmc.Proofs.CallExtraction
import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractionWellFormed

/-! Multi-argument TMC extraction simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.ListExtraction
open Bvi BviTmc BviSem BvlSem

theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

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

/-- Flapjack infrastructure: append pure fields to a successful one-field frame. -/
private theorem evaluate_append_frame_success {C F : Type} (loc tag : Nat) (child : CallBlock)
    (right : List Nat) (tailValues : List Value) (env : List Value) (state next : BviState C F)
    (result : Value)
    (rightRun : ∀ s : BviState C F, evaluate (right.map Bvi.Exp.var) env s = (.val tailValues, s))
    (run : evaluate [callBlockToBvi loc (.callBlock tag [] child [])] env state = (.val [result], next)) :
    ∃ value, result = .block tag [value] ∧
      evaluate [callBlockToBvi loc (.callBlock tag [] child right)] env state =
        (.val [.block tag (tailValues.reverse ++ [value])], next) := by
  simp only [callBlockToBvi, List.map_nil, List.nil_append, List.append_nil] at run
  rw [BviSem.evaluate, BviSem.fixClock_evaluate] at run
  cases childRun : evaluate [callBlockToBvi loc child] env state with
  | mk childResult childState =>
    cases childResult with
    | err error => simp [childRun] at run
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton _ env state childState values childRun
      simp [childRun, BviTailrec.doApp_blockCons] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨value, rfl, ?_⟩
      have argsRun : evaluate ([callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env state =
          (.val (value :: tailValues), childState) := by
        change evaluateTuple (_, env, state) = _
        rw [evaluateAppend]
        simp [BviSem.evaluateTuple, childRun, rightRun]
      simp only [callBlockToBvi, List.map_nil, List.nil_append]
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
      simp [BviTailrec.doApp_blockCons]

/-- Flapjack infrastructure: appending pure fields preserves a frame error. -/
private theorem evaluate_append_frame_error {C F : Type} (loc tag : Nat) (child : CallBlock)
    (right : List Nat) (env : List Value) (state next : BviState C F)
    (error : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (run : evaluate [callBlockToBvi loc (.callBlock tag [] child [])] env state = (.err error, next)) :
    evaluate [callBlockToBvi loc (.callBlock tag [] child right)] env state = (.err error, next) := by
  simp only [callBlockToBvi, List.map_nil, List.nil_append, List.append_nil] at run
  rw [BviSem.evaluate, BviSem.fixClock_evaluate] at run
  cases childRun : evaluate [callBlockToBvi loc child] env state with
  | mk childResult childState =>
    cases childResult with
    | err childError =>
      simp [childRun] at run
      obtain ⟨rfl, rfl⟩ := run
      have argsRun : evaluate ([callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env state =
          (.err childError, childState) := by
        change evaluateTuple (_, env, state) = _
        rw [evaluateAppend]
        simp [BviSem.evaluateTuple, childRun]
      simp only [callBlockToBvi, List.map_nil, List.nil_append]
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    | val values => simp [childRun, BviTailrec.doApp_blockCons] at run

/-- Flapjack infrastructure for the source list induction when the tail is
pure and the first expression contains the recursive call. -/
theorem evaluate_head_call_case {C F : Type}
    (n loc tag : Nat) (x y : Bvi.Exp) (ys : List Bvi.Exp)
    (tailBs : List Bvi.Exp) (vs : List Nat)
    (tailExtract : extractListSource n loc tag (y :: ys) = some (tailBs, .inl vs))
    (ih : ∀ (env : List Value) (state final : BviState C F) (result : BviResult)
      (bs : List Bvi.Exp) (cb : CallBlock),
      extractOneSource n loc tag x = some (bs, .inr cb) →
      evaluate [.op (.blockOp (.cons tag)) [x]] env state = (result, final) →
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
  have pureTail := PureExtraction.evaluate_bvi_to_cb_aux_inl (C := C) (F := F)
    n loc tag (y :: ys) tailBs vs tailExtract
  obtain ⟨rfl, pureTail⟩ := pureTail
  obtain ⟨tailValues, bothRun⟩ := pureTail env bound
  have tailRun (s : BviState C F) := (bothRun s).1
  have varsRun (s : BviState C F) := (bothRun s).2
  simp only [extractListSource, tailExtract] at extracted
  cases first : extractOneSource n loc tag x with
  | none => simp [first] at extracted
  | some pair =>
    obtain ⟨firstBs, firstKind⟩ := pair
    cases firstKind with
    | inl indices => simp only [first] at extracted; split at extracted <;> simp_all
    | inr firstCb =>
      obtain ⟨child, shape⟩ := extractList_single_shape n loc tag x firstBs firstCb
        (by simpa [extractListSource] using first)
      subst firstCb
      simp [first] at extracted
      obtain ⟨rfl, rfl⟩ := extracted.symm
      cases headRun : evaluate [x] env state with
      | mk headResult headState =>
        cases headResult with
        | err error =>
          have headOp : evaluate [.op (.blockOp (.cons tag)) [x]] env state = (.err error, headState) := by
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, headRun]
          obtain ⟨argResult, next, argsRun, success, failure⟩ :=
            ih env state headState (.err error) firstBs _ first headOp bound
          have original : (SemanticPrimitivesHOL.Result.err error, headState) = (result, final) := by
            have listError : evaluate (x :: y :: ys) env state = (.err error, headState) := by
              change evaluateTuple (x :: y :: ys, env, state) = _
              rw [evaluateCons]
              simp [BviSem.evaluateTuple, headRun]
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, listError] at run
            exact run
          cases argResult with
          | err argError =>
            have same := failure argError rfl
            have bindingsRun : evaluate (firstBs ++ y :: ys) env state = (.err argError, next) := by
              change evaluateTuple (firstBs ++ y :: ys, env, state) = _
              rw [evaluateAppend]
              simp [BviSem.evaluateTuple, argsRun]
            refine ⟨.err argError, next, bindingsRun, ?_, ?_⟩
            · intro values impossible; cases impossible
            · intro other eq; cases eq; exact same.trans original
          | val headValues =>
            have bindingsRun : evaluate (firstBs ++ y :: ys) env state =
                (.val (headValues ++ tailValues), next) := by
              change evaluateTuple (firstBs ++ y :: ys, env, state) = _
              rw [evaluateAppend]
              simp [BviSem.evaluateTuple, argsRun, tailRun]
            refine ⟨.val (headValues ++ tailValues), next, bindingsRun, ?_, ?_⟩
            · intro actual eq; cases eq
              obtain ⟨frame, extended⟩ := success headValues rfl
              constructor
              · exact (evaluate_append_frame_error loc tag child _ _ next headState error
                  (extended tailValues)).trans original
              · intro extras
                have frameError := evaluate_append_frame_error loc tag child (shiftVarsSource firstBs.length vs)
                  (headValues ++ (tailValues ++ extras)) next headState error
                  (extended (tailValues ++ extras))
                simpa [List.append_assoc] using frameError.trans original
            · intro error impossible; cases impossible
        | val headValues =>
          obtain ⟨value, rfl⟩ := evaluate_singleton x env state headState headValues headRun
          have headOp : evaluate [.op (.blockOp (.cons tag)) [x]] env state =
              (.val [.block tag [value]], headState) := by
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, headRun]
            simp [BviTailrec.doApp_blockCons]
          obtain ⟨argResult, next, argsRun, success, failure⟩ :=
            ih env state headState (.val [.block tag [value]]) firstBs _ first headOp bound
          have original : (SemanticPrimitivesHOL.Result.val [.block tag (tailValues.reverse ++ [value])], headState) =
              (result, final) := by
            rw [evaluate_cons_constructor tag x (y :: ys) env state headState value headRun, tailRun headState] at run
            exact run
          cases argResult with
          | err error => have impossible := failure error rfl; cases impossible
          | val values =>
            have bindingsRun : evaluate (firstBs ++ y :: ys) env state =
                (.val (values ++ tailValues), next) := by
              change evaluateTuple (firstBs ++ y :: ys, env, state) = _
              rw [evaluateAppend]
              simp [BviSem.evaluateTuple, argsRun, tailRun]
            have count := evaluate_length firstBs env state next values argsRun
            have rightRun (extras : List Value) (s : BviState C F) :
                evaluate ((shiftVarsSource firstBs.length vs).map Bvi.Exp.var)
                  ((values ++ tailValues) ++ extras) s = (.val tailValues, s) := by
              have extended := evaluate_vars_expand_env vs tailValues s tailValues extras (varsRun s)
              have shifted := evaluate_shift_vars vs (tailValues ++ extras) s values
              simpa [shiftVarsSource, shiftVars, ← count, List.append_assoc, extended] using shifted
            refine ⟨.val (values ++ tailValues), next, bindingsRun, ?_, ?_⟩
            · intro actual eq; cases eq
              obtain ⟨frame, extended⟩ := success values rfl
              obtain ⟨v, same, appended⟩ := evaluate_append_frame_success loc tag child
                (shiftVarsSource firstBs.length vs) tailValues (values ++ tailValues) next headState
                (.block tag [value]) (by simpa using rightRun []) (extended tailValues)
              cases same
              constructor
              · exact appended.trans original
              · intro extras
                obtain ⟨v, same, appended⟩ := evaluate_append_frame_success loc tag child
                  (shiftVarsSource firstBs.length vs) tailValues ((values ++ tailValues) ++ extras)
                  next headState (.block tag [value]) (rightRun extras)
                  (by simpa [List.append_assoc] using extended (tailValues ++ extras))
                cases same
                exact appended.trans original
            · intro error impossible; cases impossible

/-- Flapjack infrastructure for the source list induction when extraction
finds its recursive call in the tail; the complete HOL theorem follows below. -/
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

mutual
private theorem evaluateOne_inr {C F : Type} (n loc tag : Nat) (e : Bvi.Exp)
    (env : List Value) (state final : BviState C F) (result : BviResult)
    (bs : List Bvi.Exp) (cb : CallBlock)
    (extracted : extractOneSource n loc tag e = some (bs, .inr cb))
    (run : evaluate [.op (.blockOp (.cons tag)) [e]] env state = (result, final))
    (bound : n ≤ env.length) :
    ∃ argResult next, evaluate bs env state = (argResult, next) ∧
      (∀ values, argResult = .val values →
        evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
        ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
      (∀ error, argResult = .err error → (argResult, next) = (result, final)) := by
  cases e with
  | call ticks dest args handler =>
    exact CallExtraction.evaluate_bvi_to_cb_aux_inr_call n loc tag ticks dest args handler
      env state final result bs cb extracted run bound
  | op op args =>
    cases op with
    | blockOp block =>
      cases block with
      | cons childTag =>
        apply CallExtraction.evaluate_bvi_to_cb_aux_inr_constructor n loc tag childTag args
          (fun env state final result bs cb extracted run bound =>
            evaluateList_inr n loc childTag args env state final result bs cb extracted run bound)
          env state final result bs cb extracted run bound
      | _ => simp only [extractOneSource] at extracted; split at extracted <;> simp_all
    | _ => simp only [extractOneSource] at extracted; split at extracted <;> simp_all
  | _ => simp only [extractOneSource] at extracted; split at extracted <;> simp_all
termination_by expBudget e
decreasing_by all_goals subst_vars; simp only [expBudget]; omega

/-- Recursive-call extraction simulates evaluation for every argument list. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_bvi_to_cb_aux_inr"
  (fmap_as_finite_support := [refs])]
theorem evaluateList_inr {C F : Type} (n loc tag : Nat) (args : List Bvi.Exp)
    (env : List Value) (state final : BviState C F) (result : BviResult)
    (bs : List Bvi.Exp) (cb : CallBlock)
    (extracted : extractListSource n loc tag args = some (bs, .inr cb))
    (run : evaluate [.op (.blockOp (.cons tag)) args] env state = (result, final))
    (bound : n ≤ env.length) :
    ∃ argResult next, evaluate bs env state = (argResult, next) ∧
      (∀ values, argResult = .val values →
        evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
        ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
      (∀ error, argResult = .err error → (argResult, next) = (result, final)) := by
  cases args with
  | nil => simp [extractListSource] at extracted
  | cons x xs =>
    cases xs with
    | nil =>
      exact evaluateOne_inr n loc tag x env state final result bs cb
        (by simpa [extractListSource] using extracted) run bound
    | cons y ys =>
      cases tail : extractListSource n loc tag (y :: ys) with
      | none => simp [extractListSource, tail] at extracted
      | some pair =>
        obtain ⟨tailBs, kind⟩ := pair
        cases kind with
        | inl vs =>
          exact evaluate_head_call_case n loc tag x y ys tailBs vs tail
            (fun env state final result bs cb extracted run bound =>
              evaluateOne_inr n loc tag x env state final result bs cb extracted run bound)
            env state final result bs cb extracted run bound
        | inr tailCb =>
          exact evaluate_tail_call_case n loc tag x y ys tailBs tailCb tail
            (fun env state final result bs cb extracted run bound =>
              evaluateList_inr n loc tag (y :: ys) env state final result bs cb extracted run bound)
            env state final result bs cb extracted run bound
termination_by listBudget args
decreasing_by all_goals subst_vars; simp only [listBudget]; omega
end

/-- The complete mutual recursive-call extraction simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_bvi_to_cb_aux_inr_lemma"
  (fmap_as_finite_support := [refs])]
theorem evaluate_inr_lemma {C F : Type} :
    (∀ (n loc tag : Nat) (e : Bvi.Exp) (env : List Value) (state final : BviState C F)
      (result : BviResult) (bs : List Bvi.Exp) (cb : CallBlock),
      extractOneSource n loc tag e = some (bs, .inr cb) →
      evaluate [.op (.blockOp (.cons tag)) [e]] env state = (result, final) →
      n ≤ env.length →
      ∃ argResult next, evaluate bs env state = (argResult, next) ∧
        (∀ values, argResult = .val values →
          evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
          ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
        (∀ error, argResult = .err error → (argResult, next) = (result, final))) ∧
    (∀ (n loc tag : Nat) (args : List Bvi.Exp) (env : List Value) (state final : BviState C F)
      (result : BviResult) (bs : List Bvi.Exp) (cb : CallBlock),
      extractListSource n loc tag args = some (bs, .inr cb) →
      evaluate [.op (.blockOp (.cons tag)) args] env state = (result, final) →
      n ≤ env.length →
      ∃ argResult next, evaluate bs env state = (argResult, next) ∧
        (∀ values, argResult = .val values →
          evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
          ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
        (∀ error, argResult = .err error → (argResult, next) = (result, final))) := by
  exact ⟨evaluateOne_inr, evaluateList_inr⟩

/-- Successful call-block conversion preserves evaluation when let-bound. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_bvi_to_cb"
  (fmap_as_finite_support := [refs])]
theorem evaluate_bvi_to_cb {C F : Type} (cb : CallBlock) (n loc : Nat) (e : Bvi.Exp)
    (env : List Value) (state final : BviState C F) (result : BviResult) (bs : List Bvi.Exp)
    (run : evaluate [e] env state = (result, final))
    (extracted : toBlockSource n loc e = some (bs, cb)) (bound : n ≤ env.length) :
    evaluate [.let bs (callBlockToBvi loc cb)] env state = (result, final) := by
  cases e with
  | call ticks dest args handler =>
    exact CallExtraction.evaluate_bvi_to_cb_call cb n loc ticks dest args handler env state final result bs
      run extracted bound
  | op op args =>
    cases op with
    | blockOp block =>
      cases block with
      | cons tag =>
        simp only [toBlockSource] at extracted
        cases source : extractListSource n loc tag args with
        | none => simp [source] at extracted
        | some pair =>
          obtain ⟨bindings, kind⟩ := pair
          cases kind with
          | inl vs => simp [source] at extracted
          | inr child =>
            simp [source] at extracted
            obtain ⟨rfl, rfl⟩ := extracted.symm
            obtain ⟨argResult, next, argsRun, success, failure⟩ :=
              evaluateList_inr n loc tag args env state final result bindings child source run bound
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
            cases argResult with
            | err error => exact failure error rfl
            | val values => exact (success values rfl).2 env
      | _ => simp [toBlockSource] at extracted
    | _ => simp [toBlockSource] at extracted
  | _ => simp [toBlockSource] at extracted

end Flapjack.Compiler.Backend.BviTmc.ListExtraction
