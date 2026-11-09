module

public import Flapjack.EvaluateProps.ClockIoFull

import Batteries.Tactic.Init
@[expose] public section

/-! Consequences of the assembled clock-and-I/O evaluator invariant.
The source evaluator and its carriers remain pending review. -/
namespace Flapjack.EvaluateProps
open Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate_decs"]
theorem isClockIoMono_evaluateDecs {σ : Type} :
    ∀ (st : State σ) env ds, isClockIoMono (fun state => evaluateDecs state env ds) st :=
  (isClockIoMono_evaluate).2.2

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_add_to_clock"]
theorem evaluate_addToClock {σ : Type} (st : State σ) (env : SemEnv Value) (es : List AstHOL.Exp)
    (next : State σ) (result : Result (List Value) Value) (extra : Nat)
    (h : evaluate st env es = (next, result) ∧ result ≠ .err (.abort .timeoutError)) :
    evaluate { st with clock := st.clock + extra } env es = ({ next with clock := next.clock + extra }, result) :=
  isClockIoMono_extra (fun state => evaluate state env es) st next result extra (fun state => (isClockIoMono_evaluate).1 state env es) h

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_match_add_to_clock"]
theorem evaluateMatch_addToClock {σ : Type} (st : State σ) (env : SemEnv Value) (value : Value)
    (clauses : List (Pat × AstHOL.Exp)) (errorValue : Value) (next : State σ)
    (result : Result (List Value) Value) (extra : Nat)
    (h : evaluateMatch st env value clauses errorValue = (next, result) ∧ result ≠ .err (.abort .timeoutError)) :
    evaluateMatch { st with clock := st.clock + extra } env value clauses errorValue =
      ({ next with clock := next.clock + extra }, result) :=
  isClockIoMono_extra (fun state => evaluateMatch state env value clauses errorValue)
    st next result extra (fun state => (isClockIoMono_evaluate).2.1 state env value clauses errorValue) h

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_add_to_clock"]
theorem evaluateDecs_addToClock {σ : Type} (st : State σ) (env : SemEnv Value) (ds : List Dec)
    (next : State σ) (result : Result (SemEnv Value) Value) (extra : Nat)
    (h : evaluateDecs st env ds = (next, result) ∧ result ≠ .err (.abort .timeoutError)) :
    evaluateDecs { st with clock := st.clock + extra } env ds = ({ next with clock := next.clock + extra }, result) :=
  isClockIoMono_extra (fun state => evaluateDecs state env ds) st next result extra (fun state => (isClockIoMono_evaluate).2.2 state env ds) h

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_add_to_clock_io_events_mono"]
theorem evaluate_addToClockIoEventsMono {σ : Type} :
    (∀ (st : State σ) env es extra,
      ioEventsMonoHOL (evaluate st env es).1.ffi (evaluate { st with clock := st.clock + extra } env es).1.ffi) ∧
    (∀ (st : State σ) env value clauses errorValue extra,
      ioEventsMonoHOL (evaluateMatch st env value clauses errorValue).1.ffi
        (evaluateMatch { st with clock := st.clock + extra } env value clauses errorValue).1.ffi) := by
  refine ⟨?_, ?_⟩
  · intro st env es extra
    exact isClockIoMono_extra_mono (fun state => evaluate state env es) st extra (fun state => (isClockIoMono_evaluate).1 state env es)
  · intro st env value clauses errorValue extra
    exact isClockIoMono_extra_mono (fun state => evaluateMatch state env value clauses errorValue)
      st extra (fun state => (isClockIoMono_evaluate).2.1 state env value clauses errorValue)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_add_to_clock_io_events_mono"]
theorem evaluateDecs_addToClockIoEventsMono {σ : Type} (extra : Nat) (st : State σ)
    (env : SemEnv Value) (ds : List Dec) :
    ioEventsMonoHOL (evaluateDecs st env ds).1.ffi (evaluateDecs { st with clock := st.clock + extra } env ds).1.ffi :=
  isClockIoMono_extra_mono (fun state => evaluateDecs state env ds) st extra (fun state => (isClockIoMono_evaluate).2.2 state env ds)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_ffi_mono_clock"]
theorem evaluateDecs_ffiMonoClock {σ : Type} (k1 k2 : Nat) (st : State σ) (env : SemEnv Value) (ds : List Dec)
    (h : k1 ≤ k2) :
    ioEventsMonoHOL (evaluateDecs { st with clock := k1 } env ds).1.ffi
      (evaluateDecs { st with clock := k2 } env ds).1.ffi := by
  have bound := evaluateDecs_addToClockIoEventsMono (k2 - k1) { st with clock := k1 } env ds
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
  have inv := (isClockIoMono_evaluate).2.2 { st with clock := k2 } env ds
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

/-- Evaluation of an empty expression list returns the unchanged state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_nil"]
theorem evaluateNil {σ : Type} (state : State σ) (env : SemEnv Value) :
    evaluate state env [] = (state, .val []) := by
  simp [evaluate]

/-- Evaluation cannot decrease the next type stamp. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_next_type_stamp_mono"]
theorem evaluateNextTypeStampMono {σ : Type} (state : State σ) (env : SemEnv Value)
    (expressions : List AstHOL.Exp) (next : State σ) (result : Result (List Value) Value)
    (value : Value) (clauses : List (Pat × AstHOL.Exp)) (errorValue : Value)
    (matchResult : Result (List Value) Value) (decs : List Dec) (decResult : Result (SemEnv Value) Value) :
    (evaluate state env expressions = (next, result) → state.nextTypeStamp ≤ next.nextTypeStamp) ∧
    (evaluateMatch state env value clauses errorValue = (next, matchResult) → state.nextTypeStamp ≤ next.nextTypeStamp) ∧
    (evaluateDecs state env decs = (next, decResult) → state.nextTypeStamp ≤ next.nextTypeStamp) := by
  refine ⟨?_, ?_, ?_⟩
  · intro run
    have inv := (isClockIoMono_evaluate (σ := σ)).1 state env expressions
    simp only [isClockIoMono, run] at inv
    exact inv.2.2.1
  · intro run
    have inv := (isClockIoMono_evaluate (σ := σ)).2.1 state env value clauses errorValue
    simp only [isClockIoMono, run] at inv
    exact inv.2.2.1
  · intro run
    have inv := (isClockIoMono_evaluate (σ := σ)).2.2 state env decs
    simp only [isClockIoMono, run] at inv
    exact inv.2.2.1

/-- Evaluation cannot decrease the next exception stamp. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_next_exn_stamp_mono"]
theorem evaluateNextExnStampMono {σ : Type} (state : State σ) (env : SemEnv Value)
    (expressions : List AstHOL.Exp) (next : State σ) (result : Result (List Value) Value)
    (value : Value) (clauses : List (Pat × AstHOL.Exp)) (errorValue : Value)
    (matchResult : Result (List Value) Value) (decs : List Dec) (decResult : Result (SemEnv Value) Value) :
    (evaluate state env expressions = (next, result) → state.nextExnStamp ≤ next.nextExnStamp) ∧
    (evaluateMatch state env value clauses errorValue = (next, matchResult) → state.nextExnStamp ≤ next.nextExnStamp) ∧
    (evaluateDecs state env decs = (next, decResult) → state.nextExnStamp ≤ next.nextExnStamp) := by
  refine ⟨?_, ?_, ?_⟩
  · intro run
    have inv := (isClockIoMono_evaluate (σ := σ)).1 state env expressions
    simp only [isClockIoMono, run] at inv
    exact inv.2.2.2.1
  · intro run
    have inv := (isClockIoMono_evaluate (σ := σ)).2.1 state env value clauses errorValue
    simp only [isClockIoMono, run] at inv
    exact inv.2.2.2.1
  · intro run
    have inv := (isClockIoMono_evaluate (σ := σ)).2.2 state env decs
    simp only [isClockIoMono, run] at inv
    exact inv.2.2.2.1

/-- Expression and match evaluation cannot shorten the reference store. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_refs_length_mono"]
theorem evaluateRefsLengthMono {σ : Type} :
    (∀ (state : State σ) env expressions next result,
      evaluate state env expressions = (next, result) → state.refs.length ≤ next.refs.length) ∧
    (∀ (state : State σ) env value clauses errorValue next result,
      evaluateMatch state env value clauses errorValue = (next, result) → state.refs.length ≤ next.refs.length) := by
  constructor
  · intro state env expressions next result run
    have inv := (isClockIoMono_evaluate (σ := σ)).1 state env expressions
    simp only [isClockIoMono, run] at inv
    exact inv.2.2.2.2.1
  · intro state env value clauses errorValue next result run
    have inv := (isClockIoMono_evaluate (σ := σ)).2.1 state env value clauses errorValue
    simp only [isClockIoMono, run] at inv
    exact inv.2.2.2.2.1

end Flapjack.EvaluateProps
