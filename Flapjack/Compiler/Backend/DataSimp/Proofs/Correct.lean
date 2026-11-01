import Flapjack.Compiler.Backend.DataSimp
import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock

/-! Data simplification proof infrastructure. -/
namespace Flapjack.Compiler.Backend.DataSimp

/-- Sequencing with a continuation has the same result as `pSeq` when
the first program's evaluation is known not to increase its clock. The
unconditional HOL lemma still needs the full evaluator clock bound. -/
theorem evaluate_pSeq_of_clock {C F : Type} (first continuation : DataLang.Prog)
    (state : DataSem.State C F) (bound : (DataSem.evaluate first state).2.clock ≤ state.clock) :
    DataSem.evaluate (pSeq first continuation) state = DataSem.evaluate (.seq first continuation) state := by
  cases continuation <;> simp [pSeq, DataSem.evaluate_seq_skip_of_clock first state bound]

end Flapjack.Compiler.Backend.DataSimp
