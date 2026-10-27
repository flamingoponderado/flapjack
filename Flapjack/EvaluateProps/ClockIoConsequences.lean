import Flapjack.EvaluateProps.ClockIoFull

/-! Consequences of the assembled clock-and-I/O evaluator invariant.
The source evaluator and its carriers remain pending review. -/
namespace Flapjack.EvaluateProps
open Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate_decs"]
theorem isClockIoMono_evaluateDecs {σ : Type} :
    ∀ (st : State σ) env ds, isClockIoMono (fun state => evaluateDecs state env ds) st :=
  clockIoDecsFull

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_add_to_clock"]
theorem evaluate_addToClock {σ : Type} (st : State σ) (env : SemEnv Value) (es : List AstHOL.Exp)
    (next : State σ) (result : Result (List Value) Value) (extra : Nat)
    (h : evaluate st env es = (next, result) ∧ result ≠ .err (.abort .timeoutError)) :
    evaluate { st with clock := st.clock + extra } env es = ({ next with clock := next.clock + extra }, result) :=
  isClockIoMono_extra (fun state => evaluate state env es) (fun state => clockIoEvaluateFull state env es) st next result extra h

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_match_add_to_clock"]
theorem evaluateMatch_addToClock {σ : Type} (st : State σ) (env : SemEnv Value) (value : Value)
    (clauses : List (Pat × AstHOL.Exp)) (errorValue : Value) (next : State σ)
    (result : Result (List Value) Value) (extra : Nat)
    (h : evaluateMatch st env value clauses errorValue = (next, result) ∧ result ≠ .err (.abort .timeoutError)) :
    evaluateMatch { st with clock := st.clock + extra } env value clauses errorValue =
      ({ next with clock := next.clock + extra }, result) :=
  isClockIoMono_extra (fun state => evaluateMatch state env value clauses errorValue)
    (fun state => clockIoMatchFull state env value clauses errorValue) st next result extra h

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_add_to_clock"]
theorem evaluateDecs_addToClock {σ : Type} (st : State σ) (env : SemEnv Value) (ds : List Dec)
    (next : State σ) (result : Result (SemEnv Value) Value) (extra : Nat)
    (h : evaluateDecs st env ds = (next, result) ∧ result ≠ .err (.abort .timeoutError)) :
    evaluateDecs { st with clock := st.clock + extra } env ds = ({ next with clock := next.clock + extra }, result) :=
  isClockIoMono_extra (fun state => evaluateDecs state env ds) (fun state => clockIoDecsFull state env ds) st next result extra h

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_add_to_clock_io_events_mono"]
theorem evaluate_addToClockIoEventsMono {σ : Type} :
    (∀ (st : State σ) env es extra,
      ioEventsMonoHOL (evaluate st env es).1.ffi (evaluate { st with clock := st.clock + extra } env es).1.ffi) ∧
    (∀ (st : State σ) env value clauses errorValue extra,
      ioEventsMonoHOL (evaluateMatch st env value clauses errorValue).1.ffi
        (evaluateMatch { st with clock := st.clock + extra } env value clauses errorValue).1.ffi) := by
  refine ⟨?_, ?_⟩
  · intro st env es extra
    exact isClockIoMono_extra_mono (fun state => evaluate state env es) (fun state => clockIoEvaluateFull state env es) st extra
  · intro st env value clauses errorValue extra
    exact isClockIoMono_extra_mono (fun state => evaluateMatch state env value clauses errorValue)
      (fun state => clockIoMatchFull state env value clauses errorValue) st extra

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_add_to_clock_io_events_mono"]
theorem evaluateDecs_addToClockIoEventsMono {σ : Type} (st : State σ) (env : SemEnv Value)
    (ds : List Dec) (extra : Nat) :
    ioEventsMonoHOL (evaluateDecs st env ds).1.ffi (evaluateDecs { st with clock := st.clock + extra } env ds).1.ffi :=
  isClockIoMono_extra_mono (fun state => evaluateDecs state env ds) (fun state => clockIoDecsFull state env ds) st extra

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_ffi_mono_clock"]
theorem evaluateDecs_ffiMonoClock {σ : Type} (k1 k2 : Nat) (st : State σ) (env : SemEnv Value) (ds : List Dec)
    (h : k1 ≤ k2) :
    ioEventsMonoHOL (evaluateDecs { st with clock := k1 } env ds).1.ffi
      (evaluateDecs { st with clock := k2 } env ds).1.ffi := by
  have bound := evaluateDecs_addToClockIoEventsMono { st with clock := k1 } env ds (k2 - k1)
  have eq : k1 + (k2 - k1) = k2 := by omega
  simpa only [eq] using bound

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_clock_determ"]
theorem evaluateDecs_clockDeterm {σ : Type} (st : State σ) (env : SemEnv Value) (ds : List Dec)
    (s1 : State σ) (r1 : Result (SemEnv Value) Value) (s2 : State σ) (r2 : Result (SemEnv Value) Value)
    (k1 k2 : Nat)
    (h : evaluateDecs { st with clock := k1 } env ds = (s1, r1) ∧
      evaluateDecs { st with clock := k2 } env ds = (s2, r2)) :
    match r1, r2 with
    | .err (.abort .timeoutError), .err (.abort .timeoutError) => True
    | .err (.abort .timeoutError), _ => k1 < k2
    | _, .err (.abort .timeoutError) => k2 < k1
    | _, _ => s1.ffi = s2.ffi ∧ r1 = r2 := by
  have inv := clockIoDecsFull { st with clock := k2 } env ds
  simp only [isClockIoMono, h.2] at inv
  rcases inv with ⟨_, _, _, _, _, compare⟩
  specialize compare k1
  simp only [h.1] at compare
  have firstTimeout : r1 = .err (.abort .timeoutError) → r2 ≠ .err (.abort .timeoutError) → k1 < k2 := by
    intro h1 h2
    have notGe : ¬ k1 ≥ k2 - s2.clock := by
      intro ge
      exact ((compare.2.1 h2).mp ge) h1
    omega
  have secondTimeout : r1 ≠ .err (.abort .timeoutError) → r2 = .err (.abort .timeoutError) → k2 < k1 := by
    intro h1 h2
    by_contra notlt
    have le : k1 ≤ k2 := by omega
    exact (compare.2.2.1 h1 le) h2
  have agree : r1 ≠ .err (.abort .timeoutError) → r2 ≠ .err (.abort .timeoutError) →
      s1.ffi = s2.ffi ∧ r1 = r2 := by
    intro h1 h2
    obtain ⟨resultEq, stateEq⟩ := compare.1 h1 h2
    have ffiEq := congrArg (fun state : State σ => state.ffi) stateEq
    exact ⟨ffiEq, resultEq⟩
  repeat' first | split | simp_all

end Flapjack.EvaluateProps
