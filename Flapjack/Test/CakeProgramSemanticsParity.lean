import Flapjack.SemanticsHOL

/-! Basic observations of the clock-indexed CakeML source semantics. -/
namespace Flapjack.Test.CakeProgramSemanticsParity
open Flapjack Flapjack.SemanticsHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

example {σ : Type} (st : State σ) (env : SemEnv Value) (clock : Nat) :
    (evaluateProgWithClock st env clock []).1 = st.ffi := by
  simp [evaluateProgWithClock, EvaluateHOL.evaluateDecs]

example {σ : Type} (st : State σ) (env : SemEnv Value) :
    semanticsProg st env [] (.terminate .success st.ffi.ioEvents) := by
  refine ⟨0, st.ffi, .val { v := nsEmpty, c := nsEmpty }, ?_⟩
  simp [evaluateProgWithClock, EvaluateHOL.evaluateDecs]
  rfl

example {σ : Type} (st : State σ) (env : SemEnv Value) :
    ¬ semanticsProg st env [] .fail := by
  rintro ⟨clock, h⟩
  simp [evaluateProgWithClock, EvaluateHOL.evaluateDecs] at h

example {σ : Type} (st : State σ) (env : SemEnv Value) (trace) :
    ¬ semanticsProg st env [] (.diverge trace) := by
  rintro ⟨timeouts, _⟩
  obtain ⟨ffi, h⟩ := timeouts 0
  simp [evaluateProgWithClock, EvaluateHOL.evaluateDecs] at h

end Flapjack.Test.CakeProgramSemanticsParity
