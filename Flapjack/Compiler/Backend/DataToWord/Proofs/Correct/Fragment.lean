import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.RaiseCases
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.If
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Constant
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BoolNot
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BoolTest
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.LessConst
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockEmpty
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockTagEmpty
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockTagOutOfRange
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Construct
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Label
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Globals

/-! Inductive simulation for the currently established data-language fragment. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The outcomes currently covered by the production-backed simulation. -/
def outcomes64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat) (program : DataLang.Prog)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat)) : Prop :=
  continues64 conf secn label l1 l2 program source target locs ∨
    returns64 conf secn label l1 l2 program source target locs ∨
    timesOut64 conf secn label program source target ∨ raises64 conf secn label program source target locs

/-- Equal source and target evaluations transport the established outcomes. -/
theorem outcomes64_of_evaluations {C F : Type} (conf : Config) (secn label label' l1 l2 : Nat)
    (parent child : DataLang.Prog) (source source' : DataSem.State C F)
    (target target' : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (sourceEq : DataSem.evaluate parent source = DataSem.evaluate child source')
    (targetEq : WordSemStateFiniteExact.evaluate (compileControl64 conf secn label parent).1 target =
      WordSemStateFiniteExact.evaluate (compileControl64 conf secn label' child).1 target')
    (jumpTransport : ∀ a b next, WordSemStateFiniteExact.jumpExc target' = some (next, a, b) →
      ∃ beforeNext, WordSemStateFiniteExact.jumpExc target = some (beforeNext, a, b))
    (outcome : outcomes64 conf secn label' l1 l2 child source' target' locs) :
    outcomes64 conf secn label l1 l2 parent source target locs := by
  rcases outcome with continued | returned | timeout | raised
  · left
    simpa only [continues64, sourceEq, targetEq] using continued
  · right; left
    simpa only [returns64, sourceEq, targetEq] using returned
  · right; right; left
    simpa only [timesOut64, sourceEq, targetEq] using timeout
  · right; right; right
    obtain ⟨value, word, s, t, a, b, r1, r2, remaining, sr, tr, ⟨jumpState, jump⟩, ffi, bound, locations, after⟩ := raised
    refine ⟨value, word, s, t, a, b, r1, r2, remaining, ?_, ?_, jumpTransport a b jumpState jump, ffi, bound, locations, after⟩
    · simpa only [sourceEq] using sr
    · simpa only [targetEq] using tr

/-- If a sequence cannot return a type error, its first command cannot return
one either. -/
theorem seq_first_safe {C F : Type} (first second : DataLang.Prog) (source : DataSem.State C F)
    (safe : (DataSem.evaluate (.seq first second) source).1 ≠ some (.err (.abort .typeError))) :
    (DataSem.evaluate first source).1 ≠ some (.err (.abort .typeError)) := by
  intro bad
  cases run : DataSem.evaluate first source with
  | mk result state =>
    have eq : result = some (.err (.abort .typeError)) := by simpa [run] using bad
    subst result
    simp [DataSem.evaluate, run, DataSem.fixClock] at safe

/-- Sequential execution composes all covered outcomes while respecting
both clock clamping and restoration of the target termination depth. -/
theorem seq64_outcomes {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.seq first second) source).1 ≠ some (.err (.abort .typeError)))
    (firstOutcome : outcomes64 conf secn label l1 l2 first source target locs)
    (secondCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate second s).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf secn (compileControl64 conf secn label first).2 l1 l2 second s t locs) :
    outcomes64 conf secn label l1 l2 (.seq first second) source target locs := by
  rcases firstOutcome with continued | returned | timeout | raised
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
    exact outcomes64_of_evaluations conf secn label (compileControl64 conf secn label first).2 l1 l2
      (.seq first second) second source sourceClamped target targetClamped locs sourceEq targetEq
      (by
        intro a b next jump
        obtain ⟨mid, midJump⟩ := jumpExc_destination_of_keyEq target' targetClamped next a b
          (by exact of_eq_true (WordSemStackEq.sKeyEqRefl target'.stack)) rfl jump
        exact evaluate_continue_jumpExc_destination (compileControl64 conf secn label first).1 target target' mid a b targetRun midJump)
      (secondCorrect sourceClamped targetClamped afterClamp secondSafe)
  · exact Or.inr (Or.inl (seq64_returnFirst conf secn label l1 l2 first second source target locs related returned))
  · exact Or.inr (Or.inr (Or.inl (seq64_timeoutFirst conf secn label first second source target timeout)))
  · exact Or.inr (Or.inr (Or.inr (seq64_raiseFirst conf secn label l1 l2 first second source target locs related raised)))

/-- Source-safe conditionals inherit one of the covered outcomes from the
branch selected by their related Boolean locals. -/
theorem if64_outcomes {C F : Type} (conf : Config) (secn label l1 l2 name : Nat)
    (yes no : DataLang.Prog) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.ifThenElse name yes no) source).1 ≠ some (.err (.abort .typeError)))
    (yesCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate yes s).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf secn label l1 l2 yes s t locs)
    (noCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate no s).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf secn (compileControl64 conf secn label yes).2 l1 l2 no s t locs) :
    outcomes64 conf secn label l1 l2 (.ifThenElse name yes no) source target locs := by
  obtain ⟨value, b, sourceRun, bool⟩ := if64_source_boolean source name yes no safe
  have branch := if64_branch conf secn label l1 l2 name yes no source target locs related value b sourceRun bool
  cases b with
  | false =>
    have branchSafe : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [Bool.false_eq_true, ↓reduceIte, branch.1] using safe
    apply outcomes64_of_evaluations conf secn label (compileControl64 conf secn label yes).2 l1 l2
      (.ifThenElse name yes no) no source source target target locs
    · simpa only [Bool.false_eq_true, ↓reduceIte] using branch.1
    · simpa only [Bool.false_eq_true, ↓reduceIte] using branch.2
    · intro a b next jump
      exact ⟨next, jump⟩
    · exact noCorrect source target related branchSafe
  | true =>
    have branchSafe : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [↓reduceIte, branch.1] using safe
    apply outcomes64_of_evaluations conf secn label label l1 l2
      (.ifThenElse name yes no) yes source source target target locs
    · simpa only [↓reduceIte] using branch.1
    · simpa only [↓reduceIte] using branch.2
    · intro a b next jump
      exact ⟨next, jump⟩
    · exact yesCorrect source target related branchSafe

/-- Syntactic subset whose simulation cases have been established so far. -/
inductive VerifiedFragment : DataLang.Prog → Prop where
  | skip : VerifiedFragment .skip
  | tick : VerifiedFragment .tick
  | move (dest src : Nat) : VerifiedFragment (.move dest src)
  | globalsPtr (dest : Nat) : VerifiedFragment (.assign dest (.globOp .globalsPtr) [] none)
  | label (dest codeLabel : Nat) : VerifiedFragment (.assign dest (.label codeLabel) [] none)
  | emptyCons (dest tag : Nat) : tag < 2 ^ 64 / 16 → VerifiedFragment (.assign dest (.blockOp (.cons tag)) [] none)
  | blockTagEmpty (dest src tag : Nat) : VerifiedFragment (.assign dest (.blockOp (.tagLenEq tag 0)) [src] none)
  | blockTagOutOfRange (dest src tag : Nat) : ¬ tag < 2 ^ 64 / 16 →
      VerifiedFragment (.assign dest (.blockOp (.tagEq tag)) [src] none)
  | blockEmpty (dest src : Nat) : VerifiedFragment (.assign dest (.blockOp (.lenEq 0)) [src] none)
  | lessConst (dest src n : Nat) : VerifiedFragment (.assign dest (.intOp (.lessConstSmall n)) [src] none)
  | boolTest (dest left right : Nat) (test : AstHOL.Test) :
      VerifiedFragment (.assign dest (.blockOp (.boolTest test)) [left, right] none)
  | boolNot (dest src : Nat) : VerifiedFragment (.assign dest (.blockOp .boolNot) [src] none)
  | intConst (dest : Nat) (i : Int) : VerifiedFragment (.assign dest (.intOp (.const i)) [] none)
  | ret (names : List Nat) : VerifiedFragment (.return names)
  | raise (name : Nat) : VerifiedFragment (.raise name)
  | seq {first second : DataLang.Prog} : VerifiedFragment first → VerifiedFragment second →
      VerifiedFragment (.seq first second)
  | ite (name : Nat) {yes no : DataLang.Prog} : VerifiedFragment yes → VerifiedFragment no →
      VerifiedFragment (.ifThenElse name yes no)

/-- Every source-safe program in the established fragment is simulated by
its actual 64-bit compiled code, including arbitrary nested sequences and
conditionals. This is Flapjack-specific infrastructure: the remaining data
instructions and the unrestricted HOL compiler correspondence are open. -/
theorem verifiedFragment64 {C F : Type} (conf : Config) (secn l1 l2 : Nat)
    (program : DataLang.Prog) (fragment : VerifiedFragment program) :
    ∀ (label : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
      (locs : List (Nat × Nat)), stateRel64 conf l1 l2 source target none locs →
      (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf secn label l1 l2 program source target locs := by
  induction fragment with
  | skip =>
    intro label source target locs related _
    exact Or.inl (skip64_continues conf secn label l1 l2 source target locs related)
  | tick =>
    intro label source target locs related _
    by_cases zero : source.clock = 0
    · exact Or.inr (Or.inr (Or.inl (tick64_timesOut conf secn label l1 l2 source target locs related zero)))
    · exact Or.inl (tick64_continues conf secn label l1 l2 source target locs related zero)
  | move dest src =>
    intro label source target locs related safe
    exact Or.inl (move64_of_safe conf secn label l1 l2 source target locs related dest src safe)
  | globalsPtr dest =>
    intro label source target locs related safe
    exact Or.inl (assignGlobalsPtr64_of_safe conf secn label l1 l2 source target locs related dest safe)
  | label dest codeLabel =>
    intro label source target locs related safe
    exact Or.inl (assignLabel64_of_safe conf secn label l1 l2 source target locs related dest codeLabel safe)
  | emptyCons dest tag bound =>
    intro label source target locs related _
    exact Or.inl (assignEmptyCons64 conf secn label l1 l2 source target locs related dest tag bound)
  | blockTagEmpty dest src tag =>
    intro label source target locs related safe
    exact Or.inl (assignBlockTagEmpty64_of_safe conf secn label l1 l2 source target locs related dest src tag safe)
  | blockTagOutOfRange dest src tag bound =>
    intro label source target locs related safe
    exact Or.inl (assignBlockTagOutOfRange64_of_safe conf secn label l1 l2 source target locs related dest src tag bound safe)
  | blockEmpty dest src =>
    intro label source target locs related safe
    exact Or.inl (assignBlockEmpty64_of_safe conf secn label l1 l2 source target locs related dest src safe)
  | lessConst dest src n =>
    intro label source target locs related safe
    exact Or.inl (assignLessConst64_of_safe conf secn label l1 l2 source target locs related dest src n safe)
  | boolTest dest left right test =>
    intro label source target locs related safe
    exact Or.inl (assignBoolTest64_of_safe conf secn label l1 l2 source target locs related dest left right test safe)
  | boolNot dest src =>
    intro label source target locs related safe
    exact Or.inl (assignBoolNot64_of_safe conf secn label l1 l2 source target locs related dest src safe)
  | intConst dest i =>
    intro label source target locs related safe
    exact Or.inl (assignConst64_of_safe conf secn label l1 l2 source target locs related dest i safe)
  | ret names =>
    intro label source target locs related safe
    exact Or.inr (Or.inl (return64_returns_of_safe conf secn label l1 l2 source target locs related names safe))
  | raise name =>
    intro label source target locs related safe
    exact Or.inr (Or.inr (Or.inr (raise64_of_safe conf secn label l1 l2 source target locs related name safe)))
  | @seq first second firstFrag secondFrag firstIH secondIH =>
    intro label source target locs related safe
    apply seq64_outcomes conf secn label l1 l2 first second source target locs related safe
      (firstIH label source target locs related (seq_first_safe first second source safe))
    intro s t rel valid
    exact secondIH (compileControl64 conf secn label first).2 s t locs rel valid
  | @ite name yes no yesFrag noFrag yesIH noIH =>
    intro label source target locs related safe
    apply if64_outcomes conf secn label l1 l2 name yes no source target locs related safe
    · intro s t rel valid
      exact yesIH label s t locs rel valid
    · intro s t rel valid
      exact noIH (compileControl64 conf secn label yes).2 s t locs rel valid

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
