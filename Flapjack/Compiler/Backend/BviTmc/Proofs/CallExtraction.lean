import Flapjack.Compiler.Backend.BviTmc.Proofs.PureExtraction

/-! Recursive-call case of TMC constructor extraction. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallExtraction
open BviTmc BviSem BvlSem

theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- The direct-call case of the original extraction simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_bvi_to_cb_aux_inr_lemma"
  (fmap_as_finite_support := [refs])]
theorem evaluate_bvi_to_cb_aux_inr_call {C F : Type}
    (n loc tag ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp) (handler : Option Bvi.Exp)
    (env : List Value) (state final : BviState C F) (result : BviResult)
    (bs : List Bvi.Exp) (cb : CallBlock)
    (extracted : extractOneSource n loc tag (.call ticks dest args handler) = some (bs, .inr cb))
    (run : evaluate [.op (.blockOp (.cons tag)) [.call ticks dest args handler]] env state = (result, final))
    (_bound : n ≤ env.length) :
    ∃ argResult next, evaluate bs env state = (argResult, next) ∧
      (∀ values, argResult = .val values →
        evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
        ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
      (∀ error, argResult = .err error → (argResult, next) = (result, final)) := by
  simp only [extractOneSource, callToBlockSource] at extracted
  split at extracted
  next same =>
    obtain ⟨destEq, handlerEq⟩ := same
    subst dest
    subst handler
    cases binding : bind 0 args with
    | mk indices last =>
      simp only [binding, Option.map_some, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq] at extracted
      obtain ⟨rfl, rfl⟩ := extracted.symm
      cases argsRun : evaluate args env state with
      | mk argResult next =>
        refine ⟨argResult, next, rfl, ?_, ?_⟩
        · intro values valueEq
          subst argResult
          have vars := evaluate_binders args env state next values 0 last indices argsRun binding [] rfl
          have extended : ∀ extras, evaluate (indices.map Bvi.Exp.var) (values ++ extras) next =
              (.val values, next) := by
            intro extras
            exact evaluate_vars_expand_env indices values next values extras (by simpa using vars)
          have calls : ∀ extras, evaluate [.call ticks (some loc) (indices.map Bvi.Exp.var) none]
              (values ++ extras) next = evaluate [.call ticks (some loc) args none] env state := by
            intro extras
            have fixed : BviSem.fixClock state ((.val values : BviResult), next) = (.val values, next) := by
              rw [← argsRun, BviSem.fixClock_evaluate]
            rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate, argsRun, fixed]
            simp [extended extras, BviSem.fixClock]
          have reconstructed : ∀ extras, evaluate [callBlockToBvi loc (.callBlock tag [] (.rCall ticks indices) [])]
              (values ++ extras) next =
              evaluate [.op (.blockOp (.cons tag)) [.call ticks (some loc) args none]] env state := by
            intro extras
            simp only [callBlockToBvi, List.map_nil, List.nil_append, List.append_nil]
            rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate, BviSem.fixClock_evaluate, calls extras]
          constructor
          · simpa using (reconstructed []).trans run
          · intro extras
            exact (reconstructed extras).trans run
        · intro error errorEq
          subst argResult
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
          simpa using run
  next => simp at extracted

/-- The direct-call case of source reconstruction correctness. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_bvi_to_cb"
  (fmap_as_finite_support := [refs])]
theorem evaluate_bvi_to_cb_call {C F : Type}
    (cb : CallBlock) (n loc ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (handler : Option Bvi.Exp) (env : List Value) (state final : BviState C F)
    (result : BviResult) (bs : List Bvi.Exp)
    (run : evaluate [.call ticks dest args handler] env state = (result, final))
    (extracted : toBlockSource n loc (.call ticks dest args handler) = some (bs, cb))
    (_bound : n ≤ env.length) :
    evaluate [.let bs (callBlockToBvi loc cb)] env state = (result, final) := by
  simp only [toBlockSource, callToBlockSource] at extracted
  split at extracted
  next same =>
    obtain ⟨destEq, handlerEq⟩ := same
    subst dest
    subst handler
    cases binding : bind 0 args with
    | mk indices last =>
      simp only [binding, Option.some.injEq, Prod.mk.injEq] at extracted
      obtain ⟨rfl, rfl⟩ := extracted.symm
      cases argsRun : evaluate args env state with
      | mk argResult next =>
        cases argResult with
        | err error =>
          simp only [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run ⊢
          exact run
        | val values =>
          have vars := evaluate_binders args env state next values 0 last indices argsRun binding [] rfl
          have varsExtended := evaluate_vars_expand_env indices values next values env (by simpa using vars)
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
          simp only [callBlockToBvi]
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, varsExtended]
          exact run
  next => simp at extracted

/-- The constructor-expression case, using the source induction hypothesis for
the constructor's argument list. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_bvi_to_cb_aux_inr_lemma"
  (fmap_as_finite_support := [refs])]
theorem evaluate_bvi_to_cb_aux_inr_constructor {C F : Type}
    (n loc tag childTag : Nat) (args : List Bvi.Exp)
    (ih : ∀ (env : List Value) (state final : BviState C F) (result : BviResult)
      (bs : List Bvi.Exp) (cb : CallBlock),
      extractListSource n loc childTag args = some (bs, .inr cb) →
      evaluate [.op (.blockOp (.cons childTag)) args] env state = (result, final) →
      n ≤ env.length →
      ∃ argResult next, evaluate bs env state = (argResult, next) ∧
        (∀ values, argResult = .val values →
          evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
          ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
        (∀ error, argResult = .err error → (argResult, next) = (result, final)))
    (env : List Value) (state final : BviState C F) (result : BviResult)
    (bs : List Bvi.Exp) (cb : CallBlock)
    (extracted : extractOneSource n loc tag (.op (.blockOp (.cons childTag)) args) = some (bs, .inr cb))
    (run : evaluate [.op (.blockOp (.cons tag)) [.op (.blockOp (.cons childTag)) args]] env state =
      (result, final)) (bound : n ≤ env.length) :
    ∃ argResult next, evaluate bs env state = (argResult, next) ∧
      (∀ values, argResult = .val values →
        evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
        ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
      (∀ error, argResult = .err error → (argResult, next) = (result, final)) := by
  simp only [extractOneSource] at extracted
  cases innerExtract : extractListSource n loc childTag args with
  | none => simp [innerExtract] at extracted
  | some pair =>
    obtain ⟨innerBs, kind⟩ := pair
    cases kind with
    | inl vs => simp only [innerExtract] at extracted; split at extracted <;> simp_all
    | inr innerCb =>
      simp only [innerExtract, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq] at extracted
      obtain ⟨rfl, rfl⟩ := extracted.symm
      cases innerRun : evaluate [.op (.blockOp (.cons childTag)) args] env state with
      | mk innerResult innerState =>
        obtain ⟨argResult, next, argsRun, success, failure⟩ :=
          ih env state innerState innerResult innerBs innerCb innerExtract innerRun bound
        refine ⟨argResult, next, argsRun, ?_, ?_⟩
        · intro values valuesEq
          obtain ⟨headRun, extended⟩ := success values valuesEq
          have wrap (extraEnv : List Value)
              (childRun : evaluate [callBlockToBvi loc innerCb] extraEnv next = (innerResult, innerState)) :
              evaluate [callBlockToBvi loc (.callBlock tag [] innerCb [])] extraEnv next = (result, final) := by
            simp only [callBlockToBvi, List.map_nil, List.nil_append, List.append_nil]
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, childRun]
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, innerRun] at run
            exact run
          constructor
          · exact wrap values headRun
          · intro extras
            exact wrap (values ++ extras) (extended extras)
        · intro error errorEq
          have bad := failure error errorEq
          rw [← bad] at innerRun
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, innerRun] at run
          simpa [errorEq] using run

/-- The singleton-list case of the original mutual extraction simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_bvi_to_cb_aux_inr_lemma"
  (fmap_as_finite_support := [refs])]
theorem evaluate_bvi_to_cb_aux_inr_singleton {C F : Type}
    (n loc tag : Nat) (e : Bvi.Exp)
    (ih : ∀ (env : List Value) (state final : BviState C F) (result : BviResult)
      (bs : List Bvi.Exp) (cb : CallBlock),
      extractOneSource n loc tag e = some (bs, .inr cb) →
      evaluate [.op (.blockOp (.cons tag)) [e]] env state = (result, final) →
      n ≤ env.length →
      ∃ argResult next, evaluate bs env state = (argResult, next) ∧
        (∀ values, argResult = .val values →
          evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
          ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
        (∀ error, argResult = .err error → (argResult, next) = (result, final)))
    (env : List Value) (state final : BviState C F) (result : BviResult)
    (bs : List Bvi.Exp) (cb : CallBlock)
    (extracted : extractListSource n loc tag [e] = some (bs, .inr cb))
    (run : evaluate [.op (.blockOp (.cons tag)) [e]] env state = (result, final))
    (bound : n ≤ env.length) :
    ∃ argResult next, evaluate bs env state = (argResult, next) ∧
      (∀ values, argResult = .val values →
        evaluate [callBlockToBvi loc cb] values next = (result, final) ∧
        ∀ extras, evaluate [callBlockToBvi loc cb] (values ++ extras) next = (result, final)) ∧
      (∀ error, argResult = .err error → (argResult, next) = (result, final)) :=
  ih env state final result bs cb (by simpa [extractListSource] using extracted) run bound

end Flapjack.Compiler.Backend.BviTmc.CallExtraction
