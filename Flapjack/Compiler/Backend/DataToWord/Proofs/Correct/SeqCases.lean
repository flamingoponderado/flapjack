import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Seq
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Skip
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Tick
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Return

/-! Connecting instruction cases to the sequential simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- `skip` supplies a continuing simulation for sequential composition. -/
theorem skip64_continues {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) :
    continues64 conf secn label l1 l2 .skip source target locs := by
  have h := skip64 conf secn label l1 l2 source target locs related
  exact ⟨source, target, h.1, h.2.1, h.2.2.2⟩

/-- A positive-clock `tick` supplies a continuing simulation. -/
theorem tick64_continues {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (positive : source.clock ≠ 0) : continues64 conf secn label l1 l2 .tick source target locs := by
  have h := tick64_positive conf secn label l1 l2 source target locs related positive
  exact ⟨DataSem.decClock source, WordSemStateFiniteExact.decClock target, h.1, h.2.1, h.2.2.2⟩

/-- A return with successful source lookups supplies a returning simulation. -/
theorem return64_returns {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names : List Nat) (values : List DataSem.Value) (run : DataSem.getVars names source.locals = some values) :
    returns64 conf secn label l1 l2 (.return names) source target locs := by
  obtain ⟨words, size, sr, tr, bound, last⟩ := return64 conf secn label l1 l2 source target locs related names values run
  exact ⟨values, words, DataSem.flushState false source, WordSemStateFiniteExact.flushState false target, size, sr, tr, last⟩

/-- Excluding the source type-error outcome is enough to establish the
return case for any related state. -/
theorem return64_returns_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names : List Nat) (safe : (DataSem.evaluate (.return names) source).1 ≠ some (.err (.abort .typeError))) :
    returns64 conf secn label l1 l2 (.return names) source target locs := by
  cases run : DataSem.getVars names source.locals with
  | none => simp [DataSem.evaluate, run] at safe
  | some values => exact return64_returns conf secn label l1 l2 source target locs related names values run

/-- A source-safe `skip; return` program is simulated through the actual
sequential compiler and both evaluators. -/
theorem skipReturn64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names : List Nat) (safe : (DataSem.evaluate (.seq .skip (.return names)) source).1 ≠ some (.err (.abort .typeError))) :
    returns64 conf secn label l1 l2 (.seq .skip (.return names)) source target locs := by
  apply seq64_returnSecond conf secn label l1 l2 .skip (.return names) source target locs related
    (skip64_continues conf secn label l1 l2 source target locs related) safe
  intro s t rel valid
  exact return64_returns_of_safe conf secn (compileControl64 conf secn label .skip).2 l1 l2 s t locs rel names valid

/-- A zero-clock `tick` supplies the timeout simulation. -/
theorem tick64_timesOut {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (zero : source.clock = 0) : timesOut64 conf secn label .tick source target := by
  have h := tick64_timeout conf secn label l1 l2 source target locs related zero
  exact ⟨DataSem.flushState true source, WordSemStateFiniteExact.flushState true target, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
