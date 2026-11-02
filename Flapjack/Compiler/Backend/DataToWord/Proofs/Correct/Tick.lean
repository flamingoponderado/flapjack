import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

/-! The tick cases of the production-backed 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- With a positive clock, source and compiled tick both continue with one
less clock unit and preserve the candidate relation. -/
theorem tick64_positive {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (positive : source.clock ≠ 0) :
    DataSem.evaluate .tick source = (none, DataSem.decClock source) ∧
    WordSemStateFiniteExact.evaluate (compileControl64 conf secn label .tick).1 target =
      (none, WordSemStateFiniteExact.decClock target) ∧
    BackendProps.optionLe (WordSemStateFiniteExact.decClock target).stackMax (DataSem.decClock source).stackMax ∧
    stateRel64 conf l1 l2 (DataSem.decClock source) (WordSemStateFiniteExact.decClock target) none locs := by
  have sameClock : target.clock = source.clock := related.2.1
  have targetPositive : target.clock ≠ 0 := sameClock ▸ positive
  have decreased := stateRel64_withClock conf l1 l2 source target none locs (source.clock - 1) related
  refine ⟨?_, ?_, related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  · simp [DataSem.evaluate, positive]
  · simp [compileControl64, compileControl?, WordSemStateFiniteExact.evaluate, targetPositive]
  · simpa [DataSem.decClock, WordSemStateFiniteExact.decClock, sameClock] using decreased

/-- At zero clock both executions time out; flushing preserves their FFI and
stack-bound observations. -/
theorem tick64_timeout {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (zero : source.clock = 0) :
    DataSem.evaluate .tick source = (some (.err (.abort .timeoutError)), DataSem.flushState true source) ∧
    WordSemStateFiniteExact.evaluate (compileControl64 conf secn label .tick).1 target =
      (some .timeOut, WordSemStateFiniteExact.flushState true target) ∧
    (WordSemStateFiniteExact.flushState true target).ffi = (DataSem.flushState true source).ffi ∧
    BackendProps.optionLe (WordSemStateFiniteExact.flushState true target).stackMax (DataSem.flushState true source).stackMax := by
  have targetZero : target.clock = 0 := related.2.1.trans zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, zero]
  · simp [compileControl64, compileControl?, WordSemStateFiniteExact.evaluate, targetZero]
  · exact related.1
  · exact related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
