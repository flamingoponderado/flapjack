import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Boolean
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.SeqCases

/-! Conditional branch selection for the 64-bit data-to-word compiler. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The two Boolean recognizers are disjoint. -/
theorem isBool_opposite (b : Bool) (value : DataSem.Value) (h : DataSem.isBool b value = true) :
    DataSem.isBool (!b) value = false := by
  cases value with
  | block stamp tag values =>
    cases values with
    | nil => cases b <;> simp [DataSem.isBool, BackendCommon.boolToTag, BackendCommon.trueTag,
        BackendCommon.falseTag] at h ⊢ <;> omega
    | cons value values => simp [DataSem.isBool] at h
  | number n => simp [DataSem.isBool] at h
  | word64 w => simp [DataSem.isBool] at h
  | codePtr n => simp [DataSem.isBool] at h
  | refPtr flag n => simp [DataSem.isBool] at h

/-- The production compiler threads the label counter through both branches. -/
theorem compileControl64_if (conf : Config) (secn label name : Nat) (yes no : DataLang.Prog) :
    compileControl64 conf secn label (.ifThenElse name yes no) =
      let yes' := compileControl64 conf secn label yes
      let no' := compileControl64 conf secn yes'.2 no
      (.ite .equal (adjustVar name) (.imm 18) yes'.1 no'.1, no'.2) := by
  unfold compileControl64 at ⊢
  simp only [compileControl?]
  rw [compileControl64_checked conf secn label yes]
  simp only [bind, Option.bind, Option.getD]
  rw [compileControl64_checked conf secn (compileControl64 conf secn label yes).2 no]
  rfl

/-- Given a related Boolean local, source and generated word code take the
same branch without modifying the states. -/
theorem if64_branch {C F : Type} (conf : Config) (secn label l1 l2 name : Nat)
    (yes no : DataLang.Prog) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (value : DataSem.Value) (b : Bool) (sourceRun : DataSem.getVar name source.locals = some value)
    (isBool : DataSem.isBool b value = true) :
    DataSem.evaluate (.ifThenElse name yes no) source = DataSem.evaluate (if b then yes else no) source ∧
    WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.ifThenElse name yes no)).1 target =
      WordSemStateFiniteExact.evaluate (if b then (compileControl64 conf secn label yes).1 else
        (compileControl64 conf secn (compileControl64 conf secn label yes).2 no).1) target := by
  have word := stateRel64_getBool conf l1 l2 source target locs related name value b sourceRun isBool
  have opposite := isBool_opposite b value isBool
  cases b with
  | false =>
    change DataSem.isBool true value = false at opposite
    simp [DataSem.evaluate, sourceRun, isBool, opposite, compileControl64_if,
      WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
      Compiler.Encoders.Asm.wordCmpHOL, word]
  | true =>
    simp [DataSem.evaluate, sourceRun, isBool, compileControl64_if,
      WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
      Compiler.Encoders.Asm.wordCmpHOL, word]

/-- A conditional that does not raise a source type error has a Boolean
condition in its source locals. -/
theorem if64_source_boolean {C F : Type} (source : DataSem.State C F) (name : Nat) (yes no : DataLang.Prog)
    (safe : (DataSem.evaluate (.ifThenElse name yes no) source).1 ≠ some (.err (.abort .typeError))) :
    ∃ value b, DataSem.getVar name source.locals = some value ∧ DataSem.isBool b value = true := by
  cases run : DataSem.getVar name source.locals with
  | none => simp [DataSem.evaluate, run] at safe
  | some value =>
    cases yesBool : DataSem.isBool true value with
    | true => exact ⟨value, true, rfl, yesBool⟩
    | false =>
      cases noBool : DataSem.isBool false value with
      | true => exact ⟨value, false, rfl, noBool⟩
      | false => simp [DataSem.evaluate, run, yesBool, noBool] at safe

/-- Source-safe conditionals inherit a returning simulation from the selected
branch, using the label assigned to that branch by the actual compiler. -/
theorem if64_returns {C F : Type} (conf : Config) (secn label l1 l2 name : Nat)
    (yes no : DataLang.Prog) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.ifThenElse name yes no) source).1 ≠ some (.err (.abort .typeError)))
    (yesCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate yes s).1 ≠ some (.err (.abort .typeError)) →
      returns64 conf secn label l1 l2 yes s t locs)
    (noCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate no s).1 ≠ some (.err (.abort .typeError)) →
      returns64 conf secn (compileControl64 conf secn label yes).2 l1 l2 no s t locs) :
    returns64 conf secn label l1 l2 (.ifThenElse name yes no) source target locs := by
  obtain ⟨value, b, sourceRun, bool⟩ := if64_source_boolean source name yes no safe
  have branch := if64_branch conf secn label l1 l2 name yes no source target locs related value b sourceRun bool
  cases b with
  | false =>
    have branchSafe : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [Bool.false_eq_true, ↓reduceIte, branch.1] using safe
    obtain ⟨values, words, source', target', size, sourceEval, targetEval, last⟩ :=
      noCorrect source target related branchSafe
    refine ⟨values, words, source', target', size, ?_, ?_, last⟩
    · simpa only [Bool.false_eq_true, ↓reduceIte] using branch.1.trans sourceEval
    · simpa only [Bool.false_eq_true, ↓reduceIte] using branch.2.trans targetEval
  | true =>
    have branchSafe : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [↓reduceIte, branch.1] using safe
    obtain ⟨values, words, source', target', size, sourceEval, targetEval, last⟩ :=
      yesCorrect source target related branchSafe
    refine ⟨values, words, source', target', size, ?_, ?_, last⟩
    · simpa only [↓reduceIte] using branch.1.trans sourceEval
    · simpa only [↓reduceIte] using branch.2.trans targetEval

/-- A source-safe conditional inherits a continuing simulation from the
selected branch. -/
theorem if64_continues {C F : Type} (conf : Config) (secn label l1 l2 name : Nat)
    (yes no : DataLang.Prog) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.ifThenElse name yes no) source).1 ≠ some (.err (.abort .typeError)))
    (yesCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate yes s).1 ≠ some (.err (.abort .typeError)) →
      continues64 conf secn label l1 l2 yes s t locs)
    (noCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate no s).1 ≠ some (.err (.abort .typeError)) →
      continues64 conf secn (compileControl64 conf secn label yes).2 l1 l2 no s t locs) :
    continues64 conf secn label l1 l2 (.ifThenElse name yes no) source target locs := by
  obtain ⟨value, b, sourceRun, bool⟩ := if64_source_boolean source name yes no safe
  have branch := if64_branch conf secn label l1 l2 name yes no source target locs related value b sourceRun bool
  cases b with
  | false =>
    have branchSafe : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [Bool.false_eq_true, ↓reduceIte, branch.1] using safe
    obtain ⟨source', target', sourceEval, targetEval, last⟩ := noCorrect source target related branchSafe
    refine ⟨source', target', ?_, ?_, last⟩
    · simpa only [Bool.false_eq_true, ↓reduceIte] using branch.1.trans sourceEval
    · simpa only [Bool.false_eq_true, ↓reduceIte] using branch.2.trans targetEval
  | true =>
    have branchSafe : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [↓reduceIte, branch.1] using safe
    obtain ⟨source', target', sourceEval, targetEval, last⟩ := yesCorrect source target related branchSafe
    refine ⟨source', target', ?_, ?_, last⟩
    · simpa only [↓reduceIte] using branch.1.trans sourceEval
    · simpa only [↓reduceIte] using branch.2.trans targetEval

/-- A source-safe conditional inherits a timeout simulation from the
selected branch. -/
theorem if64_timesOut {C F : Type} (conf : Config) (secn label l1 l2 name : Nat)
    (yes no : DataLang.Prog) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.ifThenElse name yes no) source).1 ≠ some (.err (.abort .typeError)))
    (yesCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate yes s).1 ≠ some (.err (.abort .typeError)) →
      timesOut64 conf secn label yes s t)
    (noCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate no s).1 ≠ some (.err (.abort .typeError)) →
      timesOut64 conf secn (compileControl64 conf secn label yes).2 no s t) :
    timesOut64 conf secn label (.ifThenElse name yes no) source target := by
  obtain ⟨value, b, sourceRun, bool⟩ := if64_source_boolean source name yes no safe
  have branch := if64_branch conf secn label l1 l2 name yes no source target locs related value b sourceRun bool
  cases b with
  | false =>
    have branchSafe : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [Bool.false_eq_true, ↓reduceIte, branch.1] using safe
    obtain ⟨source', target', sourceEval, targetEval, ffi, bound⟩ := noCorrect source target related branchSafe
    refine ⟨source', target', ?_, ?_, ffi, bound⟩
    · simpa only [Bool.false_eq_true, ↓reduceIte] using branch.1.trans sourceEval
    · simpa only [Bool.false_eq_true, ↓reduceIte] using branch.2.trans targetEval
  | true =>
    have branchSafe : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [↓reduceIte, branch.1] using safe
    obtain ⟨source', target', sourceEval, targetEval, ffi, bound⟩ := yesCorrect source target related branchSafe
    refine ⟨source', target', ?_, ?_, ffi, bound⟩
    · simpa only [↓reduceIte] using branch.1.trans sourceEval
    · simpa only [↓reduceIte] using branch.2.trans targetEval

/-- A source-safe conditional returning from either branch is simulated by
the generated word conditional, including its branch-specific label counter. -/
theorem ifReturns64 {C F : Type} (conf : Config) (secn label l1 l2 name : Nat)
    (yesNames noNames : List Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.ifThenElse name (.return yesNames) (.return noNames)) source).1 ≠
      some (.err (.abort .typeError))) :
    returns64 conf secn label l1 l2 (.ifThenElse name (.return yesNames) (.return noNames)) source target locs := by
  apply if64_returns conf secn label l1 l2 name (.return yesNames) (.return noNames) source target locs related safe
  · intro s t rel valid
    exact return64_returns_of_safe conf secn label l1 l2 s t locs rel yesNames valid
  · intro s t rel valid
    exact return64_returns_of_safe conf secn (compileControl64 conf secn label (.return yesNames)).2
      l1 l2 s t locs rel noNames valid

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
