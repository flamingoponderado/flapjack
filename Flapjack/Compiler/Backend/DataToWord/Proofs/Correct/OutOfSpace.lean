import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.MakeSpaceGc
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.If
import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceMonotonicity

/-! Composing allocation failure with continuing commands. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Flapjack simulation infrastructure for the permitted allocation failure:
target events are a prefix of source events, and resource bounds hold. -/
def outOfSpace64 {C F : Type} (conf : Config) (secn label : Nat)
    (program : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) : Prop :=
  ∃ final, WordSemStateFiniteExact.evaluate (compileControl64 conf secn label program).1 target =
      (some .notEnoughSpace, final) ∧
    BackendProps.optionLe final.stackMax (DataSem.evaluate program source).2.stackMax ∧
    final.ffi.ioEvents <+: (DataSem.evaluate program source).2.ffi.ioEvents ∧
    (conf.gcKind ≠ .none → (DataSem.evaluate program source).2.safeForSpace = false)

/-- A non-type-error `makeSpace` has either a related continuation or the
actual allocation-failure outcome. -/
theorem makeSpace64_continue_or_outOfSpace {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (amount : Nat) (live : NumSet)
    (safe : (DataSem.evaluate (.makeSpace amount live) source).1 ≠ some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.makeSpace amount live) source target locs ∨
      outOfSpace64 conf secn label (.makeSpace amount live) source target := by
  cases run : DataSem.evaluate (.makeSpace amount live) source with
  | mk result sourceNext =>
    have notType : result ≠ some (.err (.abort .typeError)) := by simpa [run] using safe
    obtain ⟨targetResult, targetNext, targetRun, bound, fail, normal⟩ :=
      makeSpace64_case conf secn label l1 l2 source target locs related amount live result sourceNext run notType
    by_cases exhausted : targetResult = some .notEnoughSpace
    · right
      obtain ⟨events, unsafeProof⟩ := fail exhausted
      exact ⟨targetNext, by simpa [exhausted] using targetRun, by simpa [run] using bound,
        by simpa [run] using events, by simpa [run] using unsafeProof⟩
    · left
      obtain ⟨resultEq, targetEq, rel⟩ := normal exhausted
      exact ⟨sourceNext, targetNext, by simpa [resultEq] using run,
        by simpa [targetEq] using targetRun, rel⟩

/-- If the first command continues in related states and the second runs out
of space, the whole compiled sequence has the same failure outcome. Both
source and target clock clamps are accounted for. -/
theorem seq64_outOfSpaceSecond {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (firstCorrect : continues64 conf secn label l1 l2 first source target locs)
    (safe : (DataSem.evaluate (.seq first second) source).1 ≠ some (.err (.abort .typeError)))
    (secondCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs →
      (DataSem.evaluate second s).1 ≠ some (.err (.abort .typeError)) →
      outOfSpace64 conf secn (compileControl64 conf secn label first).2 second s t) :
    outOfSpace64 conf secn label (.seq first second) source target := by
  obtain ⟨source', target', sourceRun, targetRun, afterFirst⟩ := firstCorrect
  let k := min source.clock source'.clock
  let sourceClamped := { source' with clock := k }
  let targetClamped := { target' with clock := k, termdep := target.termdep }
  have afterClamp : stateRel64 conf l1 l2 sourceClamped targetClamped none locs :=
    stateRel64_withClock conf l1 l2 source' target' none locs k afterFirst
  have sourceEq : DataSem.evaluate (.seq first second) source = DataSem.evaluate second sourceClamped := by
    simp [DataSem.evaluate, sourceRun, DataSem.fixClock, sourceClamped, k]
  have secondSafe : (DataSem.evaluate second sourceClamped).1 ≠ some (.err (.abort .typeError)) := by
    simpa only [sourceEq] using safe
  obtain ⟨final, finalRun, bound, events, unsafeProof⟩ := secondCorrect sourceClamped targetClamped afterClamp secondSafe
  have targetEq : WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.seq first second)).1 target =
      WordSemStateFiniteExact.evaluate (compileControl64 conf secn (compileControl64 conf secn label first).2 second).1 targetClamped := by
    have oldClock : target.clock = source.clock := related.2.1
    have newClock : target'.clock = source'.clock := afterFirst.2.1
    have minEq : (if source.clock < source'.clock then source.clock else source'.clock) = k := by
      dsimp [k]
      split <;> omega
    simp [compileControl64_seq, WordSemStateFiniteExact.evaluate, targetRun,
      WordSemStateFiniteExact.fixClock, oldClock, newClock, minEq, targetClamped]
  exact ⟨final, targetEq.trans finalRun, by simpa [sourceEq] using bound,
    by simpa [sourceEq] using events, by simpa [sourceEq] using unsafeProof⟩

/-- Failure in the first compiled command propagates through the sequence,
provided the source continuation satisfies the three monotonicity induction
properties. No target execution of the second command is assumed. -/
theorem seq64_outOfSpaceFirst {C F : Type} (conf : Config) (secn label : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F)
    (firstFailure : outOfSpace64 conf secn label first source target)
    (secondMono : ∀ state : DataSem.State C F, DataSem.ResourceMono second state) :
    outOfSpace64 conf secn label (.seq first second) source target := by
  obtain ⟨firstTarget, targetRun, bound, events, unsafeProof⟩ := firstFailure
  let final := (WordSemStateFiniteExact.fixClock target
    ((some .notEnoughSpace : Option (WordSemResult 64)), firstTarget)).2
  have targetSeq : WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.seq first second)).1 target =
      (some .notEnoughSpace, final) := by
    simp [compileControl64_seq, WordSemStateFiniteExact.evaluate, targetRun, final,
      WordSemStateFiniteExact.fixClock]
  cases sourceRun : DataSem.evaluate first source with
  | mk result middle =>
    have sourceFacts : BackendProps.optionLe firstTarget.stackMax middle.stackMax ∧
        firstTarget.ffi.ioEvents <+: middle.ffi.ioEvents ∧
        (conf.gcKind ≠ .none → middle.safeForSpace = false) := by
      simpa [sourceRun] using And.intro bound (And.intro events unsafeProof)
    cases result with
    | some result =>
      refine ⟨final, targetSeq, ?_, ?_, ?_⟩
      · simpa [DataSem.evaluate, sourceRun, DataSem.fixClock, final, WordSemStateFiniteExact.fixClock] using sourceFacts.1
      · simpa [DataSem.evaluate, sourceRun, DataSem.fixClock, final, WordSemStateFiniteExact.fixClock] using sourceFacts.2.1
      · simpa [DataSem.evaluate, sourceRun, DataSem.fixClock] using sourceFacts.2.2
    | none =>
      let clamped := { middle with clock := min source.clock middle.clock }
      have seqRun : DataSem.evaluate (.seq first second) source = DataSem.evaluate second clamped := by
        simp [DataSem.evaluate, sourceRun, DataSem.fixClock, clamped]
      have nextFacts := secondMono clamped
      refine ⟨final, targetSeq, ?_, ?_, ?_⟩
      · rw [seqRun]
        exact BackendProps.optionLe_trans _ _ _ ⟨sourceFacts.1, nextFacts.2.1⟩
      · rw [seqRun]
        exact List.IsPrefix.trans sourceFacts.2.1 nextFacts.1
      · rw [seqRun]
        intro active
        have wasUnsafe := sourceFacts.2.2 active
        cases safe : (DataSem.evaluate second clamped).2.safeForSpace with
        | false => rfl
        | true =>
          have beforeSafe := nextFacts.2.2 safe
          simp [clamped, wasUnsafe] at beforeSafe

/-- A conditional inherits allocation failure from its selected branch,
with the compiler's branch-specific label counter. -/
theorem if64_outOfSpace {C F : Type} (conf : Config) (secn label l1 l2 name : Nat)
    (yes no : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.ifThenElse name yes no) source).1 ≠ some (.err (.abort .typeError)))
    (yesCorrect : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) →
      outOfSpace64 conf secn label yes source target)
    (noCorrect : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) →
      outOfSpace64 conf secn (compileControl64 conf secn label yes).2 no source target) :
    outOfSpace64 conf secn label (.ifThenElse name yes no) source target := by
  obtain ⟨value, b, sourceRun, bool⟩ := if64_source_boolean source name yes no safe
  have branch := if64_branch conf secn label l1 l2 name yes no source target locs related value b sourceRun bool
  cases b with
  | false =>
    have sourceEq : DataSem.evaluate (.ifThenElse name yes no) source = DataSem.evaluate no source := by
      simpa only [Bool.false_eq_true, ↓reduceIte] using branch.1
    have targetEq : WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.ifThenElse name yes no)).1 target =
        WordSemStateFiniteExact.evaluate (compileControl64 conf secn (compileControl64 conf secn label yes).2 no).1 target := by
      simpa only [Bool.false_eq_true, ↓reduceIte] using branch.2
    have branchSafe : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [sourceEq] using safe
    obtain ⟨final, run, bound, events, unsafeProof⟩ := noCorrect branchSafe
    exact ⟨final, targetEq.trans run, by simpa [sourceEq] using bound,
      by simpa [sourceEq] using events, by simpa [sourceEq] using unsafeProof⟩
  | true =>
    have sourceEq : DataSem.evaluate (.ifThenElse name yes no) source = DataSem.evaluate yes source := by
      simpa only [↓reduceIte] using branch.1
    have targetEq : WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.ifThenElse name yes no)).1 target =
        WordSemStateFiniteExact.evaluate (compileControl64 conf secn label yes).1 target := by
      simpa only [↓reduceIte] using branch.2
    have branchSafe : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [sourceEq] using safe
    obtain ⟨final, run, bound, events, unsafeProof⟩ := yesCorrect branchSafe
    exact ⟨final, targetEq.trans run, by simpa [sourceEq] using bound,
      by simpa [sourceEq] using events, by simpa [sourceEq] using unsafeProof⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
