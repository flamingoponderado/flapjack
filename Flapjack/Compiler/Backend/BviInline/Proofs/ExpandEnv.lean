import Flapjack.Compiler.Backend.BviInline.Proofs.TickSemantics
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateLength

/-! Environment-extension cases for BVI evaluation. -/
namespace Flapjack.Compiler.Backend.BviInline.ExpandEnv
open BviSem BvlSem

/-- Flapjack infrastructure: evaluation is unchanged by appending to a
non-type-error environment. -/
def Property {C F : Type} (xs : List Bvi.Exp) (env : List Value) (state : BviState C F) : Prop :=
  ∀ extra, (evaluate xs env state).1 ≠ .err (.abort .typeError) →
    evaluate xs (env ++ extra) state = evaluate xs env state

/-- Flapjack infrastructure: the empty expression-list case. -/
theorem nil {C F : Type} (env : List Value) (state : BviState C F) : Property [] env state := by
  intro extra _
  simp [evaluate]

/-- Flapjack infrastructure: the variable case uses the original successful
environment lookup. -/
theorem var {C F : Type} (index : Nat) (env : List Value) (state : BviState C F) :
    Property [.var index] env state := by
  intro extra notType
  cases found : env[index]? with
  | none => simp [evaluate, found] at notType
  | some value =>
    have bound : index < env.length := (List.getElem?_eq_some_iff.mp found).1
    simp [evaluate, List.getElem?_append, bound]

/-- Flapjack infrastructure: a force uses the same existing environment
entry, and any thunk call runs in the thunk's own environment. -/
theorem force {C F : Type} (location index : Nat) (env : List Value) (state : BviState C F) :
    Property [.force location index] env state := by
  intro extra notType
  cases found : env[index]? with
  | none => simp [evaluate, found] at notType
  | some value =>
    have bound : index < env.length := (List.getElem?_eq_some_iff.mp found).1
    simp [evaluate, List.getElem?_append, bound]

/-- Flapjack infrastructure: a tick reduces to its body at a smaller clock. -/
theorem tick {C F : Type} (body : Bvi.Exp) (env : List Value) (state : BviState C F)
    (bodyIH : state.clock ≠ 0 → Property [body] env (BviSem.decClock 1 state)) :
    Property [.tick body] env state := by
  intro extra notType
  by_cases zero : state.clock = 0
  · simp [evaluate, zero]
  · have bodyNotType : (evaluate [body] env (BviSem.decClock 1 state)).1 ≠ .err (.abort .typeError) := by
      simpa [evaluate, zero] using notType
    simpa [evaluate, zero] using bodyIH zero extra bodyNotType

/-- Flapjack infrastructure: extending the environment of a raised body
preserves the enclosing raise, using the body induction case. -/
theorem raiseExp {C F : Type} (body : Bvi.Exp) (env : List Value) (state : BviState C F)
    (bodyIH : Property [body] env state) : Property [.raise body] env state := by
  intro extra notType
  cases bodyRun : evaluate [body] env state with
  | mk result next =>
    have bodyNotType : (evaluate [body] env state).1 ≠ .err (.abort .typeError) := by
      cases result with
      | val values => simp [bodyRun]
      | err error => simpa [evaluate, bodyRun] using notType
    have same := bodyIH extra bodyNotType
    simp only [evaluate, same]

/-- Flapjack infrastructure: the multiple-return case propagates errors and
uses the same successfully evaluated values. -/
theorem returnExp {C F : Type} (args : List Bvi.Exp) (env : List Value) (state : BviState C F)
    (argsIH : Property args env state) : Property [.return args] env state := by
  intro extra notType
  cases argsRun : evaluate args env state with
  | mk result next =>
    have argsNotType : (evaluate args env state).1 ≠ .err (.abort .typeError) := by
      cases result with
      | val values => simp [argsRun]
      | err error => simpa [evaluate, argsRun] using notType
    have same := argsIH extra argsNotType
    simp only [evaluate, same]

/-- Flapjack infrastructure: primitive arguments can be extended before
applying the unchanged operation to their values. -/
theorem op {C F : Type} (operator : ClosLang.Op) (args : List Bvi.Exp) (env : List Value)
    (state : BviState C F) (argsIH : Property args env state) : Property [.op operator args] env state := by
  intro extra notType
  cases argsRun : evaluate args env state with
  | mk result next =>
    have argsNotType : (evaluate args env state).1 ≠ .err (.abort .typeError) := by
      cases result with
      | val values => simp [argsRun]
      | err error =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
        simpa [argsRun] using h
    have same := argsIH extra argsNotType
    simp only [evaluate, same]

/-- Flapjack infrastructure: sequential expression lists extend the
environment when their head and subsequent tail satisfy the induction cases. -/
theorem consCons {C F : Type} (first second : Bvi.Exp) (rest : List Bvi.Exp)
    (env : List Value) (state : BviState C F) (headIH : Property [first] env state)
    (tailIH : ∀ values next, evaluate [first] env state = (.val values, next) →
      Property (second :: rest) env next) : Property (first :: second :: rest) env state := by
  intro extra notType
  cases headRun : evaluate [first] env state with
  | mk headResult middle =>
    have headNotType : (evaluate [first] env state).1 ≠ .err (.abort .typeError) := by
      cases headResult with
      | val values => simp [headRun]
      | err error =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, headRun] at h
        simpa [headRun] using h
    have headSame := headIH extra headNotType
    cases headResult with
    | err error =>
      rw [evaluate, BviSem.fixClock_evaluate, headSame, headRun]
      simp
      rw [evaluate, BviSem.fixClock_evaluate, headRun]
    | val values =>
      have tailNotType : (evaluate (second :: rest) env middle).1 ≠ .err (.abort .typeError) := by
        intro bad
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, headRun] at h
        simp only at h
        cases tailRun : evaluate (second :: rest) env middle with
        | mk tailResult final =>
          rw [tailRun] at bad h
          simp at bad
          subst tailResult
          simp at h
      have tailSame := tailIH values middle headRun extra tailNotType
      rw [evaluate, BviSem.fixClock_evaluate, headSame, headRun]
      simp only
      rw [tailSame]
      rw [evaluate, BviSem.fixClock_evaluate, headRun]

/-- Flapjack infrastructure: a let extends its body environment by the same
successfully evaluated bindings before any appended caller environment. -/
theorem letExp {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp) (env : List Value)
    (state : BviState C F) (bindingsIH : Property bindings env state)
    (bodyIH : ∀ values next, evaluate bindings env state = (.val values, next) → Property [body] (values ++ env) next) :
    Property [.let bindings body] env state := by
  intro extra notType
  cases bindingsRun : evaluate bindings env state with
  | mk bindingResult middle =>
    have bindingsNotType : (evaluate bindings env state).1 ≠ .err (.abort .typeError) := by
      cases bindingResult with
      | val values => simp [bindingsRun]
      | err error =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, bindingsRun] at h
        simpa [bindingsRun] using h
    have same := bindingsIH extra bindingsNotType
    cases bindingResult with
    | err error =>
      rw [evaluate, BviSem.fixClock_evaluate, same, bindingsRun]
      simp
      rw [evaluate, BviSem.fixClock_evaluate, bindingsRun]
    | val values =>
      have bodyNotType : (evaluate [body] (values ++ env) middle).1 ≠ .err (.abort .typeError) := by
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, bindingsRun] at h
        simpa using h
      have bodySame := bodyIH values middle bindingsRun extra bodyNotType
      rw [evaluate, BviSem.fixClock_evaluate, same, bindingsRun]
      simp only
      rw [← List.append_assoc, bodySame]
      rw [evaluate, BviSem.fixClock_evaluate, bindingsRun]

/-- Flapjack infrastructure: a conditional extends its environment when
the condition and the selected branch satisfy their induction cases. -/
theorem ifThenElse {C F : Type} (condition yes no : Bvi.Exp) (env : List Value) (state : BviState C F)
    (conditionIH : Property [condition] env state)
    (branchIH : ∀ values next, evaluate [condition] env state = (.val values, next) →
      Property [yes] env next ∧ Property [no] env next) : Property [.ifThenElse condition yes no] env state := by
  intro extra notType
  cases conditionRun : evaluate [condition] env state with
  | mk conditionResult middle =>
    have conditionNotType : (evaluate [condition] env state).1 ≠ .err (.abort .typeError) := by
      cases conditionResult with
      | val values => simp [conditionRun]
      | err error =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, conditionRun] at h
        simpa [conditionRun] using h
    have same := conditionIH extra conditionNotType
    cases conditionResult with
    | err error =>
      rw [evaluate, BviSem.fixClock_evaluate, same, conditionRun]
      simp
      rw [evaluate, BviSem.fixClock_evaluate, conditionRun]
    | val values =>
      obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton condition env state middle values conditionRun
      cases selected : asBool value with
      | none =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, conditionRun] at h
        change (match asBool value with
          | none => ((.err (.abort .typeError) : BviResult), middle)
          | some true => evaluate [yes] env middle
          | some false => evaluate [no] env middle).1 ≠ .err (.abort .typeError) at h
        simp [selected] at h
      | some choice =>
        cases choice with
        | false =>
          have branchNotType : (evaluate [no] env middle).1 ≠ .err (.abort .typeError) := by
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, conditionRun] at h
            change (match asBool value with
              | none => ((.err (.abort .typeError) : BviResult), middle)
              | some true => evaluate [yes] env middle
              | some false => evaluate [no] env middle).1 ≠ .err (.abort .typeError) at h
            simpa [selected] using h
          have branchSame := (branchIH [value] middle conditionRun).2 extra branchNotType
          rw [evaluate, BviSem.fixClock_evaluate, same, conditionRun]
          change (match asBool value with
            | none => ((.err (.abort .typeError) : BviResult), middle)
            | some true => evaluate [yes] (env ++ extra) middle
            | some false => evaluate [no] (env ++ extra) middle) = _
          simp only [selected]
          rw [branchSame, evaluate, BviSem.fixClock_evaluate, conditionRun]
          change _ = (match asBool value with
            | none => ((.err (.abort .typeError) : BviResult), middle)
            | some true => evaluate [yes] env middle
            | some false => evaluate [no] env middle)
          simp [selected]
        | true =>
          have branchNotType : (evaluate [yes] env middle).1 ≠ .err (.abort .typeError) := by
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, conditionRun] at h
            change (match asBool value with
              | none => ((.err (.abort .typeError) : BviResult), middle)
              | some true => evaluate [yes] env middle
              | some false => evaluate [no] env middle).1 ≠ .err (.abort .typeError) at h
            simpa [selected] using h
          have branchSame := (branchIH [value] middle conditionRun).1 extra branchNotType
          rw [evaluate, BviSem.fixClock_evaluate, same, conditionRun]
          change (match asBool value with
            | none => ((.err (.abort .typeError) : BviResult), middle)
            | some true => evaluate [yes] (env ++ extra) middle
            | some false => evaluate [no] (env ++ extra) middle) = _
          simp only [selected]
          rw [branchSame, evaluate, BviSem.fixClock_evaluate, conditionRun]
          change _ = (match asBool value with
            | none => ((.err (.abort .typeError) : BviResult), middle)
            | some true => evaluate [yes] env middle
            | some false => evaluate [no] env middle)
          simp [selected]

/-- Flapjack infrastructure: a call without a handler evaluates its callee in
the same argument environment after extending the caller environment. -/
theorem callNone {C F : Type} (ticks : Nat) (destination : Option Nat) (args : List Bvi.Exp)
    (env : List Value) (state : BviState C F) (argsIH : Property args env state) :
    Property [.call ticks destination args none] env state := by
  intro extra notType
  cases argsRun : evaluate args env state with
  | mk result next =>
    have argsNotType : (evaluate args env state).1 ≠ .err (.abort .typeError) := by
      cases result with
      | val values => simp [argsRun]
      | err error =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
        simpa [argsRun] using h
    have same := argsIH extra argsNotType
    simp only [evaluate, same]

/-- Flapjack infrastructure: let-call continuation environments extend after
the returned values, using the continuation induction at the resulting clock. -/
theorem letCall {C F : Type} (rets ticks destination : Nat) (args : List Bvi.Exp) (body : Bvi.Exp)
    (env : List Value) (state : BviState C F) (argsIH : Property args env state)
    (bodyIH : ∀ returned (next : BviState C F), next.clock ≤ state.clock → Property [body] (returned ++ env) next) :
    Property [.letCall rets ticks destination args body] env state := by
  intro extra notType
  cases argsRun : evaluate args env state with
  | mk result middle =>
    have argsNotType : (evaluate args env state).1 ≠ .err (.abort .typeError) := by
      cases result with
      | val values => simp [argsRun]
      | err error =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
        simpa [argsRun] using h
    have same := argsIH extra argsNotType
    cases result with
    | err error =>
      rw [evaluate, BviSem.fixClock_evaluate, same, argsRun]
      simp
      rw [evaluate, BviSem.fixClock_evaluate, argsRun]
    | val values =>
      cases found : findCode (some destination) values middle.code with
      | none =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
        simp [found] at h
      | some pair =>
        obtain ⟨callArgs, callee⟩ := pair
        by_cases timeout : middle.clock < ticks + 1
        · rw [evaluate, BviSem.fixClock_evaluate, same, argsRun]
          simp [found, timeout]
          rw [evaluate, BviSem.fixClock_evaluate, argsRun]
          simp [found, timeout]
        · cases calleeRun : evaluate [callee] callArgs (BviSem.decClock (ticks + 1) middle) with
          | mk calleeResult calleeFinal =>
            cases calleeResult with
            | val values =>
              have h := notType
              rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
              simp only [found, timeout, ↓reduceIte] at h
              rw [BviSem.fixClock_evaluate, calleeRun] at h
              simp at h
            | err error =>
              cases error with
              | abort reason =>
                rw [evaluate, BviSem.fixClock_evaluate, same, argsRun]
                simp only [found, timeout, ↓reduceIte]
                rw [BviSem.fixClock_evaluate, calleeRun]
                rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                simp only [found, timeout, ↓reduceIte]
                rw [BviSem.fixClock_evaluate, calleeRun]
              | raise payload =>
                cases payload with
                | exn value =>
                  rw [evaluate, BviSem.fixClock_evaluate, same, argsRun]
                  simp only [found, timeout, ↓reduceIte]
                  rw [BviSem.fixClock_evaluate, calleeRun]
                  rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                  simp only [found, timeout, ↓reduceIte]
                  rw [BviSem.fixClock_evaluate, calleeRun]
                | ret returned =>
                  by_cases length : returned.length = rets
                  · have bodyNotType : (evaluate [body] (returned ++ env) calleeFinal).1 ≠ .err (.abort .typeError) := by
                      have h := notType
                      rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
                      simp only [found, timeout, ↓reduceIte] at h
                      rw [BviSem.fixClock_evaluate, calleeRun] at h
                      simpa [length] using h
                    have argsClock := evaluate_clock_le args env state
                    rw [argsRun] at argsClock
                    have calleeClock := evaluate_clock_le [callee] callArgs (BviSem.decClock (ticks + 1) middle)
                    rw [calleeRun] at calleeClock
                    have clock : calleeFinal.clock ≤ state.clock := by
                      simp only at argsClock calleeClock
                      simp only [BviSem.decClock] at calleeClock
                      omega
                    have bodySame := bodyIH returned calleeFinal clock extra bodyNotType
                    rw [evaluate, BviSem.fixClock_evaluate, same, argsRun]
                    simp only [found, timeout, ↓reduceIte]
                    rw [BviSem.fixClock_evaluate, calleeRun]
                    simp only [length, ↓reduceIte]
                    rw [← List.append_assoc, bodySame, evaluate, BviSem.fixClock_evaluate, argsRun]
                    simp only [found, timeout, ↓reduceIte]
                    rw [BviSem.fixClock_evaluate, calleeRun]
                    simp [length]
                  · have h := notType
                    rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
                    simp only [found, timeout, ↓reduceIte] at h
                    rw [BviSem.fixClock_evaluate, calleeRun] at h
                    simp [length] at h

/-- Flapjack infrastructure: direct calls with handlers preserve evaluation
under environment extension when arguments and handlers satisfy induction. -/
theorem callSome {C F : Type} (ticks destination : Nat) (args : List Bvi.Exp) (handler : Bvi.Exp)
    (env : List Value) (state : BviState C F) (argsIH : Property args env state)
    (handlerIH : ∀ raised (next : BviState C F), next.clock ≤ state.clock → Property [handler] (raised :: env) next) :
    Property [.call ticks (some destination) args (some handler)] env state := by
  intro extra notType
  cases argsRun : evaluate args env state with
  | mk result middle =>
    have argsNotType : (evaluate args env state).1 ≠ .err (.abort .typeError) := by
      cases result with
      | val values => simp [argsRun]
      | err error =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
        simpa [argsRun] using h
    have same := argsIH extra argsNotType
    cases result with
    | err error =>
      rw [evaluate, BviSem.fixClock_evaluate, same, argsRun]
      simp
      rw [evaluate, BviSem.fixClock_evaluate, argsRun]
      simp
    | val values =>
      cases found : findCode (some destination) values middle.code with
      | none =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
        simp [found] at h
      | some pair =>
        obtain ⟨callArgs, callee⟩ := pair
        by_cases timeout : middle.clock < ticks + 1
        · rw [evaluate, BviSem.fixClock_evaluate, same, argsRun]
          simp [found, timeout]
          rw [evaluate, BviSem.fixClock_evaluate, argsRun]
          simp [found, timeout]
        · cases calleeRun : evaluate [callee] callArgs (BviSem.decClock (ticks + 1) middle) with
          | mk calleeResult calleeFinal =>
            cases calleeResult with
            | val returned =>
              rw [evaluate, BviSem.fixClock_evaluate, same, argsRun]
              simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, timeout]
              rw [BviSem.fixClock_evaluate, calleeRun]
              rw [evaluate, BviSem.fixClock_evaluate, argsRun]
              simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, timeout]
              rw [BviSem.fixClock_evaluate, calleeRun]
            | err error =>
              cases error with
              | abort reason =>
                rw [evaluate, BviSem.fixClock_evaluate, same, argsRun]
                simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, timeout]
                rw [BviSem.fixClock_evaluate, calleeRun]
                rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, timeout]
                rw [BviSem.fixClock_evaluate, calleeRun]
              | raise payload =>
                cases payload with
                | ret values =>
                  have h := notType
                  rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
                  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, timeout] at h
                  rw [BviSem.fixClock_evaluate, calleeRun] at h
                  simp at h
                | exn raised =>
                  have handlerNotType : (evaluate [handler] (raised :: env) calleeFinal).1 ≠ .err (.abort .typeError) := by
                    intro bad
                    cases handlerRun : evaluate [handler] (raised :: env) calleeFinal with
                    | mk handlerResult handlerFinal =>
                      rw [handlerRun] at bad
                      simp at bad
                      subst handlerResult
                      have h := notType
                      rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
                      simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, timeout] at h
                      rw [BviSem.fixClock_evaluate, calleeRun] at h
                      simp only at h
                      rw [handlerRun] at h
                      simp at h
                  have argsClock := evaluate_clock_le args env state
                  rw [argsRun] at argsClock
                  have calleeClock := evaluate_clock_le [callee] callArgs (BviSem.decClock (ticks + 1) middle)
                  rw [calleeRun] at calleeClock
                  have clock : calleeFinal.clock ≤ state.clock := by
                    simp only at argsClock calleeClock
                    simp only [BviSem.decClock] at calleeClock
                    omega
                  have handlerSame := handlerIH raised calleeFinal clock extra handlerNotType
                  have handlerSame' : evaluate [handler] (raised :: (env ++ extra)) calleeFinal =
                      evaluate [handler] (raised :: env) calleeFinal := by
                    simpa only [List.cons_append] using handlerSame
                  rw [evaluate, BviSem.fixClock_evaluate, same, argsRun]
                  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, timeout]
                  rw [BviSem.fixClock_evaluate, calleeRun]
                  simp only
                  rw [handlerSame', evaluate, BviSem.fixClock_evaluate, argsRun]
                  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, timeout]
                  rw [BviSem.fixClock_evaluate, calleeRun]

end Flapjack.Compiler.Backend.BviInline.ExpandEnv
