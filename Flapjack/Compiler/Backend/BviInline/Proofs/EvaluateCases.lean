import Flapjack.Compiler.Backend.BviInline.Proofs.PrimitiveRelation

/-! Structural cases of the BVI inliner evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviInline.EvaluateCases
open BviSem
open BvlSem (Value)

/-- Flapjack infrastructure: a source evaluation is reproduced by every
related target expression list and state, except for source type errors. -/
def Property {C F : Type} (xs : List Bvi.Exp) (env : List Value)
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F) : Prop :=
  ∀ (target : BviState C F) (ys : List Bvi.Exp), InStateRel source target →
    List.Forall₂ (ExpRel target.code) xs ys →
    (evaluate xs env source).1 ≠ .err (.abort .typeError) →
    ∃ targetNext, evaluate ys env target = ((evaluate xs env source).1, targetNext) ∧
      InStateRel (evaluate xs env source).2 targetNext

/-- Flapjack infrastructure: the empty list does not change either state. -/
theorem nil {C F : Type} (env : List Value) (source : BviState (Spt (Nat × Bvi.Exp) × C) F) :
    Property [] env source := by
  intro target ys states expressions _
  cases expressions
  exact ⟨target, by simp [evaluate], by simpa [evaluate] using states⟩

/-- Flapjack infrastructure: related variables perform the same lookup. -/
theorem var {C F : Type} (index : Nat) (env : List Value)
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F) : Property [.var index] env source := by
  intro target ys states expressions notType
  cases expressions with
  | cons expression rest =>
    cases rest
    cases expression
    cases found : env[index]? with
    | none => simp [evaluate, found] at notType
    | some value => exact ⟨target, by simp [evaluate, found], by simpa [evaluate, found] using states⟩

/-- Flapjack infrastructure: raising a related expression preserves its
result and state, provided the expression induction case holds. -/
theorem raiseExp {C F : Type} (body : Bvi.Exp) (env : List Value)
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (bodyIH : Property [body] env source) : Property [.raise body] env source := by
  intro target ys states expressions notType
  cases expressions with
  | cons expression rest =>
    cases rest
    cases expression with
    | raise bodyRel =>
      cases bodyRun : evaluate [body] env source with
      | mk result next =>
        have bodyNotType : (evaluate [body] env source).1 ≠ .err (.abort .typeError) := by
          cases result with
          | val values => simp [bodyRun]
          | err error => simpa [evaluate, bodyRun] using notType
        obtain ⟨targetNext, targetRun, nextRel⟩ :=
          bodyIH target [_] states (.cons bodyRel .nil) bodyNotType
        rw [bodyRun] at targetRun nextRel
        refine ⟨targetNext, ?_, ?_⟩
        · cases result <;> simp [evaluate, targetRun, bodyRun]
        · cases result <;> simpa [evaluate, bodyRun] using nextRel

/-- Flapjack infrastructure: return propagates the result of related
argument lists through the evaluator's return exception. -/
theorem returnExp {C F : Type} (args : List Bvi.Exp) (env : List Value)
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (argsIH : Property args env source) : Property [.return args] env source := by
  intro target ys states expressions notType
  cases expressions with
  | cons expression rest =>
    cases rest
    cases expression with
    | returnExp argsRel =>
      cases argsRun : evaluate args env source with
      | mk result next =>
        have argsNotType : (evaluate args env source).1 ≠ .err (.abort .typeError) := by
          cases result with
          | val values => simp [argsRun]
          | err error => simpa [evaluate, argsRun] using notType
        obtain ⟨targetNext, targetRun, nextRel⟩ := argsIH target _ states argsRel argsNotType
        rw [argsRun] at targetRun nextRel
        refine ⟨targetNext, ?_, ?_⟩
        · cases result <;> simp [evaluate, targetRun, argsRun]
        · cases result <;> simpa [evaluate, argsRun] using nextRel

/-- Flapjack infrastructure: primitive application follows from the argument
induction case and the primitive-operation simulation. -/
theorem op {C F : Type} (operator : ClosLang.Op) (args : List Bvi.Exp) (env : List Value)
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (argsIH : Property args env source) : Property [.op operator args] env source := by
  intro target ys states expressions notType
  cases expressions with
  | cons expression rest =>
    cases rest
    cases expression with
    | op argsRel =>
      cases argsRun : evaluate args env source with
      | mk result next =>
        have argsNotType : (evaluate args env source).1 ≠ .err (.abort .typeError) := by
          cases result with
          | val values => simp [argsRun]
          | err error =>
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
            simpa [argsRun] using h
        obtain ⟨targetNext, targetRun, nextRel⟩ := argsIH target _ states argsRel argsNotType
        rw [argsRun] at targetRun nextRel
        cases result with
        | err error =>
          refine ⟨targetNext, ?_, ?_⟩
          · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
            simp only
            rw [evaluate, BviSem.fixClock_evaluate, argsRun]
          · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
            exact nextRel
        | val values =>
          have appRel := doApp_rel next targetNext nextRel operator values.reverse
          cases appRun : BviSem.doApp operator values.reverse next with
          | err error =>
            have errorNotType : error ≠ .abort .typeError := by
              have h := notType
              rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
              simpa [appRun] using h
            rw [appRun] at appRel
            have targetApp := appRel errorNotType
            refine ⟨targetNext, ?_, ?_⟩
            · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
              simp only
              rw [targetApp, evaluate, BviSem.fixClock_evaluate, argsRun]
              simp [appRun]
            · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
              simpa [appRun] using nextRel
          | val pair =>
            obtain ⟨value, last⟩ := pair
            rw [appRun] at appRel
            obtain ⟨targetLast, lastRel, targetApp⟩ := appRel
            refine ⟨targetLast, ?_, ?_⟩
            · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
              simp only
              rw [targetApp, evaluate, BviSem.fixClock_evaluate, argsRun]
              simp [appRun]
            · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
              simpa [appRun] using lastRel

/-- Flapjack infrastructure: related let bindings produce the same values;
the body relation survives any code installation performed by the bindings. -/
theorem letExp {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp) (env : List Value)
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (bindingsIH : Property bindings env source)
    (bodyIH : ∀ values next, evaluate bindings env source = (.val values, next) →
      Property [body] (values ++ env) next) : Property [.let bindings body] env source := by
  intro target ys states expressions notType
  cases expressions with
  | cons expression rest =>
    cases rest
    cases expression with
    | letExp bindingsRel bodyRel =>
      cases bindingsRun : evaluate bindings env source with
      | mk result next =>
        have bindingsNotType : (evaluate bindings env source).1 ≠ .err (.abort .typeError) := by
          cases result with
          | val values => simp [bindingsRun]
          | err error =>
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, bindingsRun] at h
            simpa [bindingsRun] using h
        obtain ⟨targetNext, targetRun, nextRel⟩ :=
          bindingsIH target _ states bindingsRel bindingsNotType
        rw [bindingsRun] at targetRun nextRel
        cases result with
        | err error =>
          refine ⟨targetNext, ?_, ?_⟩
          · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
            simp only
            rw [evaluate, BviSem.fixClock_evaluate, bindingsRun]
          · rw [evaluate, BviSem.fixClock_evaluate, bindingsRun]
            exact nextRel
        | val values =>
          have bodyNotType : (evaluate [body] (values ++ env) next).1 ≠ .err (.abort .typeError) := by
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, bindingsRun] at h
            exact h
          have bodyRelNext := (evaluate_expRel_mono _ env target targetNext (.val values)
            (by simpa using targetRun)).1 _ _ bodyRel
          obtain ⟨targetLast, targetBody, lastRel⟩ :=
            bodyIH values next bindingsRun targetNext [_] nextRel (.cons bodyRelNext .nil) bodyNotType
          refine ⟨targetLast, ?_, ?_⟩
          · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
            simp only
            rw [evaluate, BviSem.fixClock_evaluate, bindingsRun]
            exact targetBody
          · rw [evaluate, BviSem.fixClock_evaluate, bindingsRun]
            exact lastRel

/-- Flapjack infrastructure: sequential list evaluation transfers the head
and then the remaining expressions, allowing the code tree to grow. -/
theorem consCons {C F : Type} (first second : Bvi.Exp) (rest : List Bvi.Exp)
    (env : List Value) (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (headIH : Property [first] env source)
    (tailIH : ∀ values next, evaluate [first] env source = (.val values, next) →
      Property (second :: rest) env next) : Property (first :: second :: rest) env source := by
  intro target ys states expressions notType
  cases expressions with
  | cons headRel tailRel =>
    cases tailRel with
    | cons secondRel restRel =>
      cases headRun : evaluate [first] env source with
      | mk result next =>
        have headNotType : (evaluate [first] env source).1 ≠ .err (.abort .typeError) := by
          cases result with
          | val values => simp [headRun]
          | err error =>
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, headRun] at h
            simpa [headRun] using h
        obtain ⟨targetNext, targetRun, nextRel⟩ :=
          headIH target [_] states (.cons headRel .nil) headNotType
        rw [headRun] at targetRun nextRel
        cases result with
        | err error =>
          refine ⟨targetNext, ?_, ?_⟩
          · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
            simp only
            rw [evaluate, BviSem.fixClock_evaluate, headRun]
          · rw [evaluate, BviSem.fixClock_evaluate, headRun]
            exact nextRel
        | val values =>
          have tailNotType : (evaluate (second :: rest) env next).1 ≠ .err (.abort .typeError) := by
            intro bad
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, headRun] at h
            cases tailRun : evaluate (second :: rest) env next with
            | mk tailResult final =>
              rw [tailRun] at bad h
              simp at bad
              subst tailResult
              simp at h
          have tailRelNext := (evaluate_expRel_mono _ env target targetNext (.val values)
            (by simpa using targetRun)).2 _ _ (.cons secondRel restRel)
          obtain ⟨targetLast, targetTail, lastRel⟩ :=
            tailIH values next headRun targetNext _ nextRel tailRelNext tailNotType
          cases tailRun : evaluate (second :: rest) env next with
          | mk tailResult final =>
            rw [tailRun] at targetTail lastRel
            refine ⟨targetLast, ?_, ?_⟩
            · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
              simp only
              rw [targetTail, evaluate, BviSem.fixClock_evaluate, headRun, tailRun]
              cases tailResult <;> rfl
            · rw [evaluate, BviSem.fixClock_evaluate, headRun, tailRun]
              cases tailResult <;> exact lastRel

/-- Flapjack infrastructure: related tick expressions either time out at the
same clock or evaluate related bodies after equal clock decrements. -/
theorem tick {C F : Type} (body : Bvi.Exp) (env : List Value)
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (bodyIH : source.clock ≠ 0 → Property [body] env (BviSem.decClock 1 source)) :
    Property [.tick body] env source := by
  intro target ys states expressions notType
  cases expressions with
  | cons expression rest =>
    cases rest
    cases expression with
    | tick bodyRel =>
      by_cases zero : source.clock = 0
      · have targetZero : target.clock = 0 := by rw [states.2.1, zero]
        exact ⟨target, by simp [evaluate, zero, targetZero], by simpa [evaluate, zero] using states⟩
      · have targetNonzero : target.clock ≠ 0 := by simpa [states.2.1] using zero
        have bodyNotType : (evaluate [body] env (BviSem.decClock 1 source)).1 ≠ .err (.abort .typeError) := by
          simpa [evaluate, zero] using notType
        have decremented := inStateRel_decClock source target states 1
        obtain ⟨targetNext, targetRun, nextRel⟩ := bodyIH zero (BviSem.decClock 1 target) [_]
          decremented (.cons bodyRel .nil) bodyNotType
        exact ⟨targetNext, by simpa [evaluate, zero, targetNonzero] using targetRun,
          by simpa [evaluate, zero] using nextRel⟩

end Flapjack.Compiler.Backend.BviInline.EvaluateCases
