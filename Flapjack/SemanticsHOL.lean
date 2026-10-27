import Flapjack.EvaluateHOL.ClockFull
import Flapjack.Misc.LprefixLub

/-! CakeML program observations over the clocked source evaluator. Parsing,
typing, initial environments, and the top-level compiler theorem remain to be
ported. The definitions here are pending full source and carrier review. -/
namespace Flapjack.SemanticsHOL
open Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.AstHOL

/-- Run a source program with a supplied clock and return its FFI state and
result, as in the original observational semantics. -/
@[hol "cakeml/semantics/semanticsScript.sml" "evaluate_prog_with_clock_def"]
noncomputable def evaluateProgWithClock {σ : Type} (st : State σ) (env : SemEnv Value)
    (clock : Nat) (prog : List Dec) : HolFfiState σ × Result (SemEnv Value) Value :=
  let (next, result) := evaluateDecs { st with clock } env prog
  (next.ffi, result)

/-- Source program behaviours, retaining every clock and the original
least-upper-bound relation on the family of FFI event traces. -/
@[hol "cakeml/semantics/semanticsScript.sml" "semantics_prog_def"]
noncomputable def semanticsProg {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) : HolBehaviour → Prop
  | .terminate outcome events =>
      ∃ clock ffi result,
        evaluateProgWithClock st env clock prog = (ffi, result) ∧
        (match result with
         | .err (.abort (.ffiError event)) => outcome = .ffiOutcome event
         | _ => result ≠ .err (.abort .timeoutError) ∧ outcome = .success) ∧
        events = ffi.ioEvents ∧ result ≠ .err (.abort .typeError)
  | .diverge trace =>
      (∀ clock, ∃ ffi,
        evaluateProgWithClock st env clock prog = (ffi, .err (.abort .timeoutError))) ∧
      HolLList.lprefixLub
        (fun events => ∃ clock : Nat,
          HolLList.fromList (evaluateProgWithClock st env clock prog).1.ioEvents = events) trace
  | .fail =>
      ∃ clock, (evaluateProgWithClock st env clock prog).2 = .err (.abort .typeError)

end Flapjack.SemanticsHOL
