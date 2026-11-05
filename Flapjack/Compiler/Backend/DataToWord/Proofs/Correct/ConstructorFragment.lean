import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorAssign
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.FragmentSpace

/-! Composing constructor assignments with the established simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The space-safety flag after the first command is true whenever the
complete source sequence is space-safe. -/
theorem seq_first_space_safe {C F : Type} (first second : DataLang.Prog)
    (source : DataSem.State C F)
    (safe : (DataSem.evaluate (.seq first second) source).2.safeForSpace = true) :
    (DataSem.evaluate first source).2.safeForSpace = true := by
  cases run : DataSem.evaluate first source with
  | mk result middle =>
    cases result with
    | none =>
      let clamped := { middle with clock := min source.clock middle.clock }
      have secondSafe : (DataSem.evaluate second clamped).2.safeForSpace = true := by
        simpa [DataSem.evaluate, run, DataSem.fixClock, clamped] using safe
      have before := (DataSem.evaluate_resourceMono second clamped).2.2 secondSafe
      simpa [run, clamped] using before
    | some result =>
      simpa [DataSem.evaluate, run, DataSem.fixClock] using safe

/-- Sequential outcome composition when the continuation additionally
requires space safety of its actual source execution. -/
theorem seq64_outcomesWithSpace_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.seq first second) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.seq first second) source).2.safeForSpace = true)
    (firstOutcome : outcomesWithSpace64 conf secn label l1 l2 first source target locs)
    (secondCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs →
      (DataSem.evaluate second s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate second s).2.safeForSpace = true →
      outcomesWithSpace64 conf secn (compileControl64 conf secn label first).2 l1 l2 second s t locs) :
    outcomesWithSpace64 conf secn label l1 l2 (.seq first second) source target locs := by
  rcases firstOutcome with ordinary | failure
  · rcases ordinary with continued | returned | timeout | raised
    · obtain ⟨source', target', sourceRun, targetRun, afterFirst⟩ := continued
      let k := min source.clock source'.clock
      let sourceClamped := { source' with clock := k }
      let targetClamped := { target' with clock := k, termdep := target.termdep }
      have afterClamp : stateRel64 conf l1 l2 sourceClamped targetClamped none locs :=
        stateRel64_withClock conf l1 l2 source' target' none locs k afterFirst
      have sourceEq : DataSem.evaluate (.seq first second) source = DataSem.evaluate second sourceClamped := by
        simp [DataSem.evaluate, sourceRun, DataSem.fixClock, sourceClamped, k]
      have targetEq : WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.seq first second)).1 target =
          WordSemStateFiniteExact.evaluate (compileControl64 conf secn (compileControl64 conf secn label first).2 second).1 targetClamped := by
        have oldClock : target.clock = source.clock := related.2.1
        have newClock : target'.clock = source'.clock := afterFirst.2.1
        have minEq : (if source.clock < source'.clock then source.clock else source'.clock) = k := by
          dsimp [k]
          split <;> omega
        simp [compileControl64_seq, WordSemStateFiniteExact.evaluate, targetRun,
          WordSemStateFiniteExact.fixClock, oldClock, newClock, minEq, targetClamped]
      have secondSafe : (DataSem.evaluate second sourceClamped).1 ≠ some (.err (.abort .typeError)) := by
        simpa only [sourceEq] using safe
      have secondSpace : (DataSem.evaluate second sourceClamped).2.safeForSpace = true := by
        simpa only [sourceEq] using spaceSafe
      rcases secondCorrect sourceClamped targetClamped afterClamp secondSafe secondSpace with ordinary | failure
      · left
        apply outcomes64_of_evaluations conf secn label (compileControl64 conf secn label first).2 l1 l2
          (.seq first second) second source sourceClamped target targetClamped locs sourceEq targetEq
        · intro a b next jump
          obtain ⟨mid, midJump⟩ := jumpExc_destination_of_keyEq target' targetClamped next a b
            (by exact of_eq_true (WordSemStackEq.sKeyEqRefl target'.stack)) rfl jump
          exact evaluate_continue_jumpExc_destination (compileControl64 conf secn label first).1 target target' mid a b targetRun midJump
        · exact ordinary
      · right
        obtain ⟨final, run, bound, events, unsafeProof⟩ := failure
        exact ⟨final, targetEq.trans run, by simpa [sourceEq] using bound,
          by simpa [sourceEq] using events, by simpa [sourceEq] using unsafeProof⟩
    · exact Or.inl (Or.inr (Or.inl (seq64_returnFirst conf secn label l1 l2 first second source target locs related returned)))
    · exact Or.inl (Or.inr (Or.inr (Or.inl (seq64_timeoutFirst conf secn label first second source target timeout))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (seq64_raiseFirst conf secn label l1 l2 first second source target locs related raised))))
  · exact Or.inr (seq64_outOfSpaceFirst conf secn label first second source target failure)

/-- Conditional outcome composition with space safety of the selected
source branch. -/
theorem if64_outcomesWithSpace_safe {C F : Type} (conf : Config) (secn label l1 l2 name : Nat)
    (yes no : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.ifThenElse name yes no) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.ifThenElse name yes no) source).2.safeForSpace = true)
    (yesCorrect : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate yes source).2.safeForSpace = true →
      outcomesWithSpace64 conf secn label l1 l2 yes source target locs)
    (noCorrect : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate no source).2.safeForSpace = true →
      outcomesWithSpace64 conf secn (compileControl64 conf secn label yes).2 l1 l2 no source target locs) :
    outcomesWithSpace64 conf secn label l1 l2 (.ifThenElse name yes no) source target locs := by
  obtain ⟨value, b, sourceRun, bool⟩ := if64_source_boolean source name yes no safe
  have branch := if64_branch conf secn label l1 l2 name yes no source target locs related value b sourceRun bool
  cases b with
  | false =>
    have sourceEq : DataSem.evaluate (.ifThenElse name yes no) source = DataSem.evaluate no source := by
      simpa only [Bool.false_eq_true, ↓reduceIte] using branch.1
    have targetEq : WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.ifThenElse name yes no)).1 target =
        WordSemStateFiniteExact.evaluate (compileControl64 conf secn (compileControl64 conf secn label yes).2 no).1 target := by
      simpa only [Bool.false_eq_true, ↓reduceIte] using branch.2
    rcases noCorrect (by simpa only [sourceEq] using safe) (by simpa only [sourceEq] using spaceSafe) with ordinary | failure
    · exact Or.inl (outcomes64_of_evaluations conf secn label (compileControl64 conf secn label yes).2 l1 l2
        (.ifThenElse name yes no) no source source target target locs sourceEq targetEq
        (by intro a b next jump; exact ⟨next, jump⟩) ordinary)
    · obtain ⟨final, run, bound, events, unsafeProof⟩ := failure
      exact Or.inr ⟨final, targetEq.trans run, by simpa [sourceEq] using bound,
        by simpa [sourceEq] using events, by simpa [sourceEq] using unsafeProof⟩
  | true =>
    have sourceEq : DataSem.evaluate (.ifThenElse name yes no) source = DataSem.evaluate yes source := by
      simpa only [↓reduceIte] using branch.1
    have targetEq : WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.ifThenElse name yes no)).1 target =
        WordSemStateFiniteExact.evaluate (compileControl64 conf secn label yes).1 target := by
      simpa only [↓reduceIte] using branch.2
    rcases yesCorrect (by simpa only [sourceEq] using safe) (by simpa only [sourceEq] using spaceSafe) with ordinary | failure
    · exact Or.inl (outcomes64_of_evaluations conf secn label label l1 l2
        (.ifThenElse name yes no) yes source source target target locs sourceEq targetEq
        (by intro a b next jump; exact ⟨next, jump⟩) ordinary)
    · obtain ⟨final, run, bound, events, unsafeProof⟩ := failure
      exact Or.inr ⟨final, targetEq.trans run, by simpa [sourceEq] using bound,
        by simpa [sourceEq] using events, by simpa [sourceEq] using unsafeProof⟩

/-- The established allocation-aware fragment extended with nonempty
constructor assignments and arbitrary sequences and conditionals. -/
inductive VerifiedWithConstructors : DataLang.Prog → Prop where
  | established {program : DataLang.Prog} : VerifiedWithSpace program → VerifiedWithConstructors program
  | constructor (dest tag : Nat) (args : List Nat) : args ≠ [] →
      VerifiedWithConstructors (.assign dest (.blockOp (.cons tag)) args none)
  | seq {first second : DataLang.Prog} : VerifiedWithConstructors first → VerifiedWithConstructors second →
      VerifiedWithConstructors (.seq first second)
  | ite (name : Nat) {yes no : DataLang.Prog} : VerifiedWithConstructors yes → VerifiedWithConstructors no →
      VerifiedWithConstructors (.ifThenElse name yes no)

/-- The extended fragment has a related outcome or the permitted allocation
failure when the source execution is type-safe and space-safe. This is
Flapjack infrastructure; unrestricted pass correctness remains open. -/
theorem verifiedWithConstructors64 {C F : Type} (conf : Config) (secn l1 l2 : Nat)
    (program : DataLang.Prog) (fragment : VerifiedWithConstructors program) :
    ∀ (label : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
      (locs : List (Nat × Nat)), stateRel64 conf l1 l2 source target none locs →
      (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate program source).2.safeForSpace = true →
      outcomesWithSpace64 conf secn label l1 l2 program source target locs := by
  induction fragment with
  | established established =>
    intro label source target locs related safe _
    exact verifiedWithSpace64 conf secn l1 l2 _ established label source target locs related safe
  | constructor dest tag args nonempty =>
    intro label source target locs related safe spaceSafe
    exact Or.inl (Or.inl (assignCons64_of_safe conf secn label l1 l2 dest tag source target locs related
      args nonempty safe spaceSafe))
  | @seq first second firstFragment secondFragment firstIH secondIH =>
    intro label source target locs related safe spaceSafe
    apply seq64_outcomesWithSpace_safe conf secn label l1 l2 first second source target locs related safe spaceSafe
      (firstIH label source target locs related (seq_first_safe first second source safe)
        (seq_first_space_safe first second source spaceSafe))
    intro s t rel valid space
    exact secondIH (compileControl64 conf secn label first).2 s t locs rel valid space
  | @ite name yes no yesFragment noFragment yesIH noIH =>
    intro label source target locs related safe spaceSafe
    apply if64_outcomesWithSpace_safe conf secn label l1 l2 name yes no source target locs related safe spaceSafe
    · intro valid space
      exact yesIH label source target locs related valid space
    · intro valid space
      exact noIH (compileControl64 conf secn label yes).2 source target locs related valid space

/-- A nonempty constructor followed by any established allocation-aware
fragment is simulated, including target allocation failure in the tail.
Source type and space safety are stated for the whole sequence. -/
theorem constructorSeq_verifiedWithSpace64 {C F : Type} (conf : Config) (secn label l1 l2 dest tag : Nat)
    (args : List Nat) (nonempty : args ≠ []) (second : DataLang.Prog)
    (fragment : VerifiedWithSpace second) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (typeSafe : (DataSem.evaluate (.seq (.assign dest (.blockOp (.cons tag)) args none) second) source).1 ≠
      some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.seq (.assign dest (.blockOp (.cons tag)) args none) second) source).2.safeForSpace = true) :
    outcomesWithSpace64 conf secn label l1 l2 (.seq (.assign dest (.blockOp (.cons tag)) args none) second)
      source target locs := by
  let first := DataLang.Prog.assign dest (.blockOp (.cons tag)) args none
  have firstType : (DataSem.evaluate first source).1 ≠ some (.err (.abort .typeError)) :=
    seq_first_safe first second source typeSafe
  have firstSpace : (DataSem.evaluate first source).2.safeForSpace = true :=
    seq_first_space_safe first second source spaceSafe
  have firstRun : continues64 conf secn label l1 l2 first source target locs :=
    assignCons64_of_safe conf secn label l1 l2 dest tag source target locs related args nonempty firstType firstSpace
  apply seq64_outcomesWithSpace conf secn label l1 l2 first second source target locs related typeSafe
    (Or.inl (Or.inl firstRun))
  intro s t rel valid
  exact verifiedWithSpace64 conf secn l1 l2 second fragment (compileControl64 conf secn label first).2 s t locs rel valid

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
