import Flapjack.SemanticsProps.Clock

/-! Supporting lemmas for determinism of source-program observations. The
source evaluator and its carriers remain pending review. -/
namespace Flapjack.SemanticsProps
open Flapjack.SemanticsHOL Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.EvaluateProps Flapjack.AstHOL

/-- Flapjack helper: two completed evaluations have the same FFI state and
result, irrespective of their initial clocks. -/
theorem evaluateProgWithClock_completed {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) (k₁ k₂ : Nat)
    (h₁ : (evaluateProgWithClock st env k₁ prog).2 ≠ .err (.abort .timeoutError))
    (h₂ : (evaluateProgWithClock st env k₂ prog).2 ≠ .err (.abort .timeoutError)) :
    evaluateProgWithClock st env k₁ prog = evaluateProgWithClock st env k₂ prog := by
  generalize he₁ : evaluateDecs { st with clock := k₁ } env prog = p₁
  generalize he₂ : evaluateDecs { st with clock := k₂ } env prog = p₂
  rcases p₁ with ⟨s₁, r₁⟩
  rcases p₂ with ⟨s₂, r₂⟩
  have det := evaluateDecs_clockDeterm st env prog s₁ r₁ s₂ r₂ k₁ k₂ ⟨he₁, he₂⟩
  simp only [evaluateProgWithClock, he₁, he₂] at h₁ h₂ ⊢
  cases r₁ with
  | val v => cases r₂ with
    | val w => simp_all
    | err e => cases e with
      | raise v => simp_all
      | abort a => cases a <;> simp_all
  | err e => cases e with
    | raise v => cases r₂ with
      | val w => simp_all
      | err e => cases e with
        | raise w => simp_all
        | abort a => cases a <;> simp_all
    | abort a => cases a with
      | timeoutError => exact False.elim (h₁ rfl)
      | typeError => cases r₂ with
        | val w => simp_all
        | err e => cases e with
          | raise w => simp_all
          | abort a => cases a <;> simp_all
      | ffiError event => cases r₂ with
        | val w => simp_all
        | err e => cases e with
          | raise w => simp_all
          | abort a => cases a <;> simp_all

/-- Flapjack helper extracting a non-timeout evaluation from a termination
observation. -/
theorem terminateWitness {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) (outcome : HolOutcome) (events : List HolIoEvent)
    (h : semanticsProg st env prog (.terminate outcome events)) :
    ∃ k ffi result, evaluateProgWithClock st env k prog = (ffi, result) ∧
      result ≠ .err (.abort .timeoutError) ∧ result ≠ .err (.abort .typeError) ∧
      events = ffi.ioEvents ∧
      outcome = match result with
        | .err (.abort (.ffiError event)) => .ffiOutcome event
        | _ => .success := by
  obtain ⟨k, ffi, result, heval, houtcome, hevents, htype⟩ := h
  cases result with
  | val v => exact ⟨k, ffi, .val v, heval, houtcome.1, htype, hevents, houtcome.2⟩
  | err e => cases e with
    | raise v => exact ⟨k, ffi, .err (.raise v), heval, houtcome.1, htype, hevents, houtcome.2⟩
    | abort a => cases a with
      | typeError => exact False.elim (htype rfl)
      | timeoutError => exact False.elim (houtcome.1 rfl)
      | ffiError event => exact ⟨k, ffi, .err (.abort (.ffiError event)), heval, by simp, htype, hevents, houtcome⟩

/-- Flapjack helper: completed termination observations agree. -/
theorem terminateUnique {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) (o₁ o₂ : HolOutcome) (es₁ es₂ : List HolIoEvent)
    (h₁ : semanticsProg st env prog (.terminate o₁ es₁))
    (h₂ : semanticsProg st env prog (.terminate o₂ es₂)) :
    o₁ = o₂ ∧ es₁ = es₂ := by
  obtain ⟨k₁, ffi₁, r₁, e₁, nt₁, _, events₁, outcome₁⟩ := terminateWitness st env prog o₁ es₁ h₁
  obtain ⟨k₂, ffi₂, r₂, e₂, nt₂, _, events₂, outcome₂⟩ := terminateWitness st env prog o₂ es₂ h₂
  have agree := evaluateProgWithClock_completed st env prog k₁ k₂
    (by rw [e₁]; exact nt₁) (by rw [e₂]; exact nt₂)
  rw [e₁, e₂] at agree
  cases agree
  exact ⟨outcome₁.trans outcome₂.symm, events₁.trans events₂.symm⟩

/-- Flapjack helper: a completed termination cannot coexist with type failure. -/
theorem terminateNotFail {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) (outcome : HolOutcome) (events : List HolIoEvent)
    (h : semanticsProg st env prog (.terminate outcome events))
    (hf : semanticsProg st env prog .fail) : False := by
  obtain ⟨k, ffi, result, ev, nt, notType, _, _⟩ := terminateWitness st env prog outcome events h
  obtain ⟨k', fail⟩ := hf
  have agree := evaluateProgWithClock_completed st env prog k k'
    (by rw [ev]; exact nt) (by rw [fail]; simp)
  have results := congrArg Prod.snd agree
  rw [ev, fail] at results
  exact notType results

/-- Flapjack helper: a timeout at every clock excludes a completed result. -/
theorem divergeNotCompleted {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) (trace : HolLList HolIoEvent)
    (h : semanticsProg st env prog (.diverge trace)) (k : Nat)
    (done : (evaluateProgWithClock st env k prog).2 ≠ .err (.abort .timeoutError)) : False := by
  obtain ⟨ffi, eval⟩ := h.1 k
  apply done
  rw [eval]

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "semantics_prog_deterministic"]
theorem semanticsProg_deterministic {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) (b₁ b₂ : HolBehaviour)
    (h : semanticsProg st env prog b₁ ∧ semanticsProg st env prog b₂) : b₁ = b₂ := by
  rcases h with ⟨h₁, h₂⟩
  cases b₁ with
  | diverge t₁ =>
    cases b₂ with
    | diverge t₂ =>
      exact congrArg HolBehaviour.diverge (HolLList.unique_lprefix_lub h₁.2 h₂.2)
    | terminate outcome events =>
      obtain ⟨k, ffi, result, ev, nt, _, _, _⟩ := terminateWitness st env prog outcome events h₂
      exact False.elim (divergeNotCompleted st env prog t₁ h₁ k (by rw [ev]; exact nt))
    | fail =>
      obtain ⟨k, eval⟩ := h₂
      exact False.elim (divergeNotCompleted st env prog t₁ h₁ k (by rw [eval]; simp))
  | terminate o₁ es₁ =>
    cases b₂ with
    | diverge trace =>
      obtain ⟨k, ffi, result, ev, nt, _, _, _⟩ := terminateWitness st env prog o₁ es₁ h₁
      exact False.elim (divergeNotCompleted st env prog trace h₂ k (by rw [ev]; exact nt))
    | terminate o₂ es₂ =>
      obtain ⟨rfl, rfl⟩ := terminateUnique st env prog o₁ o₂ es₁ es₂ h₁ h₂
      rfl
    | fail => exact False.elim (terminateNotFail st env prog o₁ es₁ h₁ h₂)
  | fail =>
    cases b₂ with
    | diverge trace =>
      obtain ⟨k, eval⟩ := h₁
      exact False.elim (divergeNotCompleted st env prog trace h₂ k (by rw [eval]; simp))
    | terminate outcome events => exact False.elim (terminateNotFail st env prog outcome events h₂ h₁)
    | fail => rfl

end Flapjack.SemanticsProps
