import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Raise
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Seq

/-! Exceptional outcomes and sequential composition. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Both evaluators raise a related value and preserve the handler-state
relation when the value is installed. -/
def raises64 {C F : Type} (conf : Config) (secn label : Nat)
    (program : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat)) : Prop :=
  ∃ value word source' target' a b r1 r2 remaining,
    DataSem.evaluate program source = (some (.err (.raise value)), source') ∧
    WordSemStateFiniteExact.evaluate (compileControl64 conf secn label program).1 target =
      (some (.exception (.loc a b) word), target') ∧
    target'.ffi = source'.ffi ∧ BackendProps.optionLe target'.stackMax source'.stackMax ∧
    wordSemLastN (source'.stack.length + 1) locs = (r1, r2) :: remaining ∧
    ∀ dest, stateRel64 conf r1 r2 (DataSem.setVar dest value source')
      (WordSemStateFiniteExact.setVar (adjustVar dest) word target') none remaining

/-- A source-safe raise has a corresponding word exception. -/
theorem raise64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name : Nat) (safe : (DataSem.evaluate (.raise name) source).1 ≠ some (.err (.abort .typeError))) :
    raises64 conf secn label (.raise name) source target locs := by
  cases lookup : DataSem.getVar name source.locals with
  | none => simp [DataSem.evaluate, lookup] at safe
  | some value =>
    cases jump : DataSem.jumpExc source with
    | none => simp [DataSem.evaluate, lookup, jump] at safe
    | some next =>
      obtain ⟨word, nextTarget, a, b, r1, r2, remaining, sr, tr, ffi, bound, locations, after⟩ :=
        raise64 conf secn label l1 l2 source target locs related name value next lookup jump
      exact ⟨value, word, next, nextTarget, a, b, r1, r2, remaining, sr, tr, ffi, bound, locations, after⟩

/-- An exception in the first command propagates through a sequence, including
clock clamping and the restored handler-state relation. -/
theorem seq64_raiseFirst {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (firstRaises : raises64 conf secn label first source target locs) :
    raises64 conf secn label (.seq first second) source target locs := by
  obtain ⟨value, word, source', target', a, b, r1, r2, remaining, sr, tr, ffi, bound, locations, after⟩ := firstRaises
  let k := min source.clock source'.clock
  let sourceClamped := { source' with clock := k }
  let targetClamped := { target' with clock := k, termdep := target.termdep }
  have oldClock : target.clock = source.clock := related.2.1
  have newClock : target'.clock = source'.clock := (after 0).2.1
  have minEq : (if source.clock < source'.clock then source.clock else source'.clock) = k := by
    dsimp [k]
    split <;> omega
  refine ⟨value, word, sourceClamped, targetClamped, a, b, r1, r2, remaining, ?_, ?_, ffi, bound, locations, ?_⟩
  · simp [DataSem.evaluate, sr, DataSem.fixClock, sourceClamped, k]
  · simp [compileControl64_seq, WordSemStateFiniteExact.evaluate, tr,
      WordSemStateFiniteExact.fixClock, oldClock, newClock, minEq, targetClamped]
  · intro dest
    have h := stateRel64_withClock conf r1 r2 (DataSem.setVar dest value source')
      (WordSemStateFiniteExact.setVar (adjustVar dest) word target') none remaining k (after dest)
    exact h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
