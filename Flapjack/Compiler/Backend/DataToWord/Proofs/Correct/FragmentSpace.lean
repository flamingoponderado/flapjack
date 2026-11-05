import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Fragment

/-! Composing established data-to-word cases with allocation failure. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The established simulation outcomes extended with the real target
allocation-failure outcome. This is Flapjack-specific infrastructure. -/
def outcomesWithSpace64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (program : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat)) : Prop :=
  outcomes64 conf secn label l1 l2 program source target locs ∨
    outOfSpace64 conf secn label program source target

/-- Sequential composition for both ordinary and allocation-failure
outcomes. The continuation's monotonicity is an induction property. -/
theorem seq64_outcomesWithSpace {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.seq first second) source).1 ≠ some (.err (.abort .typeError)))
    (firstOutcome : outcomesWithSpace64 conf secn label l1 l2 first source target locs)
    (secondMono : ∀ s : DataSem.State C F, DataSem.ResourceMono second s)
    (secondCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs →
      (DataSem.evaluate second s).1 ≠ some (.err (.abort .typeError)) →
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
      rcases secondCorrect sourceClamped targetClamped afterClamp secondSafe with ordinary | failure
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
  · exact Or.inr (seq64_outOfSpaceFirst conf secn label first second source target failure secondMono)

/-- A conditional preserves either kind of outcome from the selected branch. -/
theorem if64_outcomesWithSpace {C F : Type} (conf : Config) (secn label l1 l2 name : Nat)
    (yes no : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.ifThenElse name yes no) source).1 ≠ some (.err (.abort .typeError)))
    (yesCorrect : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) →
      outcomesWithSpace64 conf secn label l1 l2 yes source target locs)
    (noCorrect : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) →
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
    have branchSafe : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [sourceEq] using safe
    rcases noCorrect branchSafe with ordinary | failure
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
    have branchSafe : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [sourceEq] using safe
    rcases yesCorrect branchSafe with ordinary | failure
    · exact Or.inl (outcomes64_of_evaluations conf secn label label l1 l2
        (.ifThenElse name yes no) yes source source target target locs sourceEq targetEq
        (by intro a b next jump; exact ⟨next, jump⟩) ordinary)
    · obtain ⟨final, run, bound, events, unsafeProof⟩ := failure
      exact Or.inr ⟨final, targetEq.trans run, by simpa [sourceEq] using bound,
        by simpa [sourceEq] using events, by simpa [sourceEq] using unsafeProof⟩


/-- Extend the previously verified fragment with arbitrary allocations and
nesting of sequences and conditionals. -/
inductive VerifiedWithSpace : DataLang.Prog → Prop where
  | established {program : DataLang.Prog} : VerifiedFragment program → VerifiedWithSpace program
  | makeSpace (amount : Nat) (live : NumSet) : VerifiedWithSpace (.makeSpace amount live)
  | seq {first second : DataLang.Prog} : VerifiedWithSpace first → VerifiedWithSpace second →
      VerifiedWithSpace (.seq first second)
  | ite (name : Nat) {yes no : DataLang.Prog} : VerifiedWithSpace yes → VerifiedWithSpace no →
      VerifiedWithSpace (.ifThenElse name yes no)

/-- The extended fragment has monotone source resources. -/
theorem verifiedWithSpace_resourceMono {C F : Type} (program : DataLang.Prog)
    (fragment : VerifiedWithSpace program) : ∀ state : DataSem.State C F, DataSem.ResourceMono program state := by
  induction fragment with
  | established established => exact verifiedFragment_resourceMono _ established
  | makeSpace amount live => exact DataSem.resourceMono_makeSpace amount live
  | @seq first second _ _ firstIH secondIH =>
    intro state
    exact DataSem.resourceMono_seq first second state (firstIH state) secondIH
  | @ite name yes no _ _ yesIH noIH =>
    intro state
    exact DataSem.resourceMono_if name yes no state (yesIH state) (noIH state)

/-- Actual compiled execution of the extended source-safe fragment has an
ordinary simulated outcome or the permitted allocation-failure outcome.
The candidate state relation and uncovered instructions remain open. -/
theorem verifiedWithSpace64 {C F : Type} (conf : Config) (secn l1 l2 : Nat)
    (program : DataLang.Prog) (fragment : VerifiedWithSpace program) :
    ∀ (label : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
      (locs : List (Nat × Nat)), stateRel64 conf l1 l2 source target none locs →
      (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
      outcomesWithSpace64 conf secn label l1 l2 program source target locs := by
  induction fragment with
  | established established =>
    intro label source target locs related safe
    exact Or.inl (verifiedFragment64 conf secn l1 l2 _ established label source target locs related safe)
  | makeSpace amount live =>
    intro label source target locs related safe
    rcases makeSpace64_continue_or_outOfSpace conf secn label l1 l2 source target locs related amount live safe with continued | failure
    · exact Or.inl (Or.inl continued)
    · exact Or.inr failure
  | @seq first second firstFragment secondFragment firstIH secondIH =>
    intro label source target locs related safe
    apply seq64_outcomesWithSpace conf secn label l1 l2 first second source target locs related safe
      (firstIH label source target locs related (seq_first_safe first second source safe))
      (verifiedWithSpace_resourceMono second secondFragment)
    intro s t rel valid
    exact secondIH (compileControl64 conf secn label first).2 s t locs rel valid
  | @ite name yes no yesFragment noFragment yesIH noIH =>
    intro label source target locs related safe
    apply if64_outcomesWithSpace conf secn label l1 l2 name yes no source target locs related safe
    · intro valid
      exact yesIH label source target locs related valid
    · intro valid
      exact noIH (compileControl64 conf secn label yes).2 source target locs related valid

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
