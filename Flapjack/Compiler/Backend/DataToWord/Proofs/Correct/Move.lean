import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LocalUpdates
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.SeqCases

/-! The move case of the production-backed 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A successful source move is simulated by the generated singleton word
move and preserves the candidate state relation. -/
theorem move64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src : Nat) (value : DataSem.Value) (sourceRun : DataSem.getVar src source.locals = some value) :
    continues64 conf secn label l1 l2 (.move dest src) source target locs := by
  obtain ⟨word, targetRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related src value sourceRun
  refine ⟨DataSem.setVar dest value source, WordSemStateFiniteExact.setVar (adjustVar dest) word target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, sourceRun]
  · simp [compileControl64, compileControl?, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.getVars, targetRun, WordSemStateFiniteExact.setVars,
      WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.sptAlistInsert]
  · exact stateRel64_setLocal conf l1 l2 source target locs related dest src value word sourceRun targetRun

/-- Excluding the source type-error result suffices for a move simulation. -/
theorem move64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src : Nat) (safe : (DataSem.evaluate (.move dest src) source).1 ≠ some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.move dest src) source target locs := by
  cases run : DataSem.getVar src source.locals with
  | none => simp [DataSem.evaluate, run] at safe
  | some value => exact move64 conf secn label l1 l2 source target locs related dest src value run

/-- A source-safe move followed by a return is simulated compositionally,
including the case where the returned list contains the moved destination. -/
theorem moveReturn64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src : Nat) (names : List Nat)
    (safe : (DataSem.evaluate (.seq (.move dest src) (.return names)) source).1 ≠ some (.err (.abort .typeError))) :
    returns64 conf secn label l1 l2 (.seq (.move dest src) (.return names)) source target locs := by
  have first : continues64 conf secn label l1 l2 (.move dest src) source target locs := by
    cases run : DataSem.getVar src source.locals with
    | none => simp [DataSem.evaluate, run, DataSem.fixClock] at safe
    | some value => exact move64 conf secn label l1 l2 source target locs related dest src value run
  apply seq64_returnSecond conf secn label l1 l2 (.move dest src) (.return names) source target locs related first safe
  intro s t rel valid
  exact return64_returns_of_safe conf secn (compileControl64 conf secn label (.move dest src)).2 l1 l2 s t locs rel names valid

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
