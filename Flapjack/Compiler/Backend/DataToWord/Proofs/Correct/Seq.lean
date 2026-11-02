import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

/-! Sequential composition of continuing 64-bit simulation cases. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Both evaluators continue and end in related states. This predicate is
Flapjack-specific infrastructure for composing simulation cases. -/
def continues64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (program : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat)) : Prop :=
  ∃ source' target', DataSem.evaluate program source = (none, source') ∧
    WordSemStateFiniteExact.evaluate (compileControl64 conf secn label program).1 target = (none, target') ∧
    stateRel64 conf l1 l2 source' target' none locs

/-- The production traversal emits a sequence of the two compiled programs,
threading its fresh-label counter through the first. -/
theorem compileControl64_seq (conf : Config) (secn label : Nat) (first second : DataLang.Prog) :
    compileControl64 conf secn label (.seq first second) =
      let first' := compileControl64 conf secn label first
      let second' := compileControl64 conf secn first'.2 second
      (.seq first'.1 second'.1, second'.2) := by
  unfold compileControl64 at ⊢
  simp only [compileControl?]
  rw [compileControl64_checked conf secn label first]
  simp only [bind, Option.bind, Option.getD]
  rw [compileControl64_checked conf secn (compileControl64 conf secn label first).2 second]
  rfl

/-- Continuing simulations compose through the source and target `fixClock`
operations. The target additionally restores its original termination depth,
which the candidate state relation does not constrain. -/
theorem seq64_continues {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (firstCorrect : continues64 conf secn label l1 l2 first source target locs)
    (secondCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F), stateRel64 conf l1 l2 s t none locs →
      continues64 conf secn (compileControl64 conf secn label first).2 l1 l2 second s t locs) :
    continues64 conf secn label l1 l2 (.seq first second) source target locs := by
  obtain ⟨source', target', sourceRun, targetRun, afterFirst⟩ := firstCorrect
  let k := min source.clock source'.clock
  let sourceClamped := { source' with clock := k }
  let targetClamped := { target' with clock := k, termdep := target.termdep }
  have afterClamp : stateRel64 conf l1 l2 sourceClamped targetClamped none locs := by
    have h := stateRel64_withClock conf l1 l2 source' target' none locs k afterFirst
    exact h
  obtain ⟨source'', target'', sourceRun', targetRun', afterSecond⟩ := secondCorrect sourceClamped targetClamped afterClamp
  refine ⟨source'', target'', ?_, ?_, afterSecond⟩
  · simp [DataSem.evaluate, sourceRun, DataSem.fixClock, sourceClamped, k, sourceRun']
  · have oldClock : target.clock = source.clock := related.2.1
    have newClock : target'.clock = source'.clock := afterFirst.2.1
    have minEq : (if source.clock < source'.clock then source.clock else source'.clock) = k := by
      dsimp [k]
      split <;> omega
    simpa [compileControl64_seq, WordSemStateFiniteExact.evaluate, targetRun,
      WordSemStateFiniteExact.fixClock, oldClock, newClock, minEq, targetClamped] using targetRun'

/-- Both evaluators return related value lists at the saved location. -/
def returns64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (program : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat)) : Prop :=
  ∃ values words source' target', values.length = words.length ∧
    DataSem.evaluate program source = (some (.val values), source') ∧
    WordSemStateFiniteExact.evaluate (compileControl64 conf secn label program).1 target =
      (some (.result (.loc l1 l2) words), target') ∧
    stateRel64 conf l1 l2 source' target' (some (values.zip words)) locs

/-- A continuing first command followed by a returning command returns the
same related values when run as a sequence. -/
theorem seq64_returnSecond {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (firstCorrect : continues64 conf secn label l1 l2 first source target locs)
    (sourceSafe : (DataSem.evaluate (.seq first second) source).1 ≠ some (.err (.abort .typeError)))
    (secondCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs →
      (DataSem.evaluate second s).1 ≠ some (.err (.abort .typeError)) →
      returns64 conf secn (compileControl64 conf secn label first).2 l1 l2 second s t locs) :
    returns64 conf secn label l1 l2 (.seq first second) source target locs := by
  obtain ⟨source', target', sourceRun, targetRun, afterFirst⟩ := firstCorrect
  let k := min source.clock source'.clock
  let sourceClamped := { source' with clock := k }
  let targetClamped := { target' with clock := k, termdep := target.termdep }
  have afterClamp : stateRel64 conf l1 l2 sourceClamped targetClamped none locs := by
    exact stateRel64_withClock conf l1 l2 source' target' none locs k afterFirst
  have secondSafe : (DataSem.evaluate second sourceClamped).1 ≠ some (.err (.abort .typeError)) := by
    simpa [DataSem.evaluate, sourceRun, DataSem.fixClock, sourceClamped, k] using sourceSafe
  obtain ⟨values, words, source'', target'', size, sourceRun', targetRun', afterSecond⟩ :=
    secondCorrect sourceClamped targetClamped afterClamp secondSafe
  refine ⟨values, words, source'', target'', size, ?_, ?_, afterSecond⟩
  · simp [DataSem.evaluate, sourceRun, DataSem.fixClock, sourceClamped, k, sourceRun']
  · have oldClock : target.clock = source.clock := related.2.1
    have newClock : target'.clock = source'.clock := afterFirst.2.1
    have minEq : (if source.clock < source'.clock then source.clock else source'.clock) = k := by
      dsimp [k]
      split <;> omega
    simpa [compileControl64_seq, WordSemStateFiniteExact.evaluate, targetRun,
      WordSemStateFiniteExact.fixClock, oldClock, newClock, minEq, targetClamped] using targetRun'

/-- If the first command returns, sequential execution skips the second command
and preserves the return relation after clock clamping. -/
theorem seq64_returnFirst {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (firstReturns : returns64 conf secn label l1 l2 first source target locs) :
    returns64 conf secn label l1 l2 (.seq first second) source target locs := by
  obtain ⟨values, words, source', target', size, sourceRun, targetRun, afterFirst⟩ := firstReturns
  let k := min source.clock source'.clock
  let sourceClamped := { source' with clock := k }
  let targetClamped := { target' with clock := k, termdep := target.termdep }
  have oldClock : target.clock = source.clock := related.2.1
  have newClock : target'.clock = source'.clock := afterFirst.2.1
  have minEq : (if source.clock < source'.clock then source.clock else source'.clock) = k := by
    dsimp [k]
    split <;> omega
  refine ⟨values, words, sourceClamped, targetClamped, size, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, sourceRun, DataSem.fixClock, sourceClamped, k]
  · simp [compileControl64_seq, WordSemStateFiniteExact.evaluate, targetRun,
      WordSemStateFiniteExact.fixClock, oldClock, newClock, minEq, targetClamped]
  · exact stateRel64_withClock conf l1 l2 source' target' (some (values.zip words)) locs k afterFirst

/-- Both evaluators time out with the same FFI and bounded target stack. -/
def timesOut64 {C F : Type} (conf : Config) (secn label : Nat)
    (program : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) : Prop :=
  ∃ source' target', DataSem.evaluate program source = (some (.err (.abort .timeoutError)), source') ∧
    WordSemStateFiniteExact.evaluate (compileControl64 conf secn label program).1 target = (some .timeOut, target') ∧
    target'.ffi = source'.ffi ∧ BackendProps.optionLe target'.stackMax source'.stackMax

/-- If the first command times out, the second command is not run. -/
theorem seq64_timeoutFirst {C F : Type} (conf : Config) (secn label : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F)
    (firstTimeout : timesOut64 conf secn label first source target) :
    timesOut64 conf secn label (.seq first second) source target := by
  obtain ⟨source', target', sourceRun, targetRun, ffi, bound⟩ := firstTimeout
  refine ⟨(DataSem.fixClock source ((), source')).2,
    (WordSemStateFiniteExact.fixClock target ((), target')).2, ?_, ?_, ffi, bound⟩
  · simp [DataSem.evaluate, sourceRun, DataSem.fixClock]
  · simp [compileControl64_seq, WordSemStateFiniteExact.evaluate, targetRun, WordSemStateFiniteExact.fixClock]

/-- A timeout in the second command propagates after a continuing first
command, with the intermediate clocks clamped as in both evaluators. -/
theorem seq64_timeoutSecond {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (firstCorrect : continues64 conf secn label l1 l2 first source target locs)
    (secondCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs →
      timesOut64 conf secn (compileControl64 conf secn label first).2 second s t) :
    timesOut64 conf secn label (.seq first second) source target := by
  obtain ⟨source', target', sourceRun, targetRun, afterFirst⟩ := firstCorrect
  let k := min source.clock source'.clock
  let sourceClamped := { source' with clock := k }
  let targetClamped := { target' with clock := k, termdep := target.termdep }
  have afterClamp : stateRel64 conf l1 l2 sourceClamped targetClamped none locs := by
    exact stateRel64_withClock conf l1 l2 source' target' none locs k afterFirst
  obtain ⟨source'', target'', sourceRun', targetRun', ffi, bound⟩ := secondCorrect sourceClamped targetClamped afterClamp
  refine ⟨source'', target'', ?_, ?_, ffi, bound⟩
  · simp [DataSem.evaluate, sourceRun, DataSem.fixClock, sourceClamped, k, sourceRun']
  · have oldClock : target.clock = source.clock := related.2.1
    have newClock : target'.clock = source'.clock := afterFirst.2.1
    have minEq : (if source.clock < source'.clock then source.clock else source'.clock) = k := by
      dsimp [k]
      split <;> omega
    simpa [compileControl64_seq, WordSemStateFiniteExact.evaluate, targetRun,
      WordSemStateFiniteExact.fixClock, oldClock, newClock, minEq, targetClamped] using targetRun'

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
