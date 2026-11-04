import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Fragment
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CallEnv

/-! Direct tail-call composition for the data-to-word simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- For a successful positive-clock direct tail call, any nonempty source
result and acceptable word result propagate from the callee unchanged. -/
theorem tailCall64_direct_evaluations {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names : List Nat) (values : List DataSem.Value) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (positive : source.clock ≠ 0) (words : List (WordLocW 64))
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words)
    (sourceResult : Option (SemanticPrimitivesHOL.Result (List DataSem.Value) DataSem.Value)) (sourceNext : DataSem.State C F)
    (targetResult : Option (WordSemResult 64)) (targetNext : WordSemStateFiniteExact 64 C F)
    (sourceBody : DataSem.evaluate body (DataSem.callEnv values size (DataSem.decClock source)) = (sourceResult, sourceNext))
    (targetBody : WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1
      (WordSemStateFiniteExact.callEnv (.loc l1 l2 :: words) size (WordSemStateFiniteExact.decClock target)) = (targetResult, targetNext))
    (nonempty : sourceResult ≠ none) (goodReturn : wordSemBadFunReturn targetResult = false) :
    DataSem.evaluate (.call none (some callee) names none) source = (sourceResult, sourceNext) ∧
    WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.call none (some callee) names none)).1 target =
      (targetResult, targetNext) := by
  obtain ⟨words', check, lengths⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  rw [wordRun] at check
  have eq : words = words' := Option.some.inj check
  subst words'
  have zero : WordSemStateFiniteExact.getVar 0 target = some (.loc l1 l2) := related.2.2.2.2.2.2.2.2.2.2.1 rfl
  have allWords : WordSemStateFiniteExact.getVars (0 :: names.map adjustVar) target = some (.loc l1 l2 :: words) := by
    simp [WordSemStateFiniteExact.getVars, zero, wordRun]
  have code := stateRel64_findCode_direct conf l1 l2 source target locs related l1 l2 callee values words body size lengths found
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  constructor
  · cases sourceResult with
    | none => contradiction
    | some result => simp [DataSem.evaluate, sourceRun, found, positive, sourceBody]
  · have compiled : (compileControl64 conf secn label (.call none (some callee) names none)).1 =
        .call none (some callee) (0 :: names.map adjustVar) none := rfl
    rw [compiled]
    simp [WordSemStateFiniteExact.evaluate, allWords, wordSemBadDestArgs, wordSemAddRetLoc,
      code, targetPositive, targetBody, goodReturn]

/-- Direct tail-call simulation composes with a simulation of the selected
callee. The callee premise is the induction hypothesis for the code body. -/
theorem tailCall64_direct_outcomes {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names : List Nat) (values : List DataSem.Value) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (positive : source.clock ≠ 0)
    (safe : (DataSem.evaluate (.call none (some callee) names none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 s t none locs →
      (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf callee 2 l1 l2 body s t locs) :
    outcomes64 conf secn label l1 l2 (.call none (some callee) names none) source target locs := by
  obtain ⟨words, wordRun, _⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  have calleeRelated := stateRel64_callEnv conf l1 l2 l1 l2 source target locs related names values words size sourceRun wordRun
  have calleeSafe : (DataSem.evaluate body (DataSem.callEnv values size (DataSem.decClock source))).1 ≠
      some (.err (.abort .typeError)) := by
    intro bad
    cases run : DataSem.evaluate body (DataSem.callEnv values size (DataSem.decClock source)) with
    | mk result state =>
      have resultEq : result = some (.err (.abort .typeError)) := by simpa [run] using bad
      subst result
      simp [DataSem.evaluate, sourceRun, found, positive, run] at safe
  rcases calleeCorrect _ _ calleeRelated calleeSafe with continued | returned | timeout | raised
  · obtain ⟨sourceNext, targetNext, sr, tr, after⟩ := continued
    simp [DataSem.evaluate, sourceRun, found, positive, sr] at safe
  · obtain ⟨result, targetValues, sourceNext, targetNext, lengths, sr, tr, after⟩ := returned
    have eqs := tailCall64_direct_evaluations conf secn label l1 l2 source target locs related callee names values body size
      sourceRun found positive words wordRun _ sourceNext _ targetNext sr tr (by simp) rfl
    exact Or.inr (Or.inl ⟨result, targetValues, sourceNext, targetNext, lengths, eqs.1, eqs.2, after⟩)
  · obtain ⟨sourceNext, targetNext, sr, tr, ffi, bound⟩ := timeout
    have eqs := tailCall64_direct_evaluations conf secn label l1 l2 source target locs related callee names values body size
      sourceRun found positive words wordRun _ sourceNext _ targetNext sr tr (by simp) rfl
    exact Or.inr (Or.inr (Or.inl ⟨sourceNext, targetNext, eqs.1, eqs.2, ffi, bound⟩))
  · obtain ⟨result, targetValue, sourceNext, targetNext, a, b, r1, r2, remaining, sr, tr, ffi, bound, locations, after⟩ := raised
    have eqs := tailCall64_direct_evaluations conf secn label l1 l2 source target locs related callee names values body size
      sourceRun found positive words wordRun _ sourceNext _ targetNext sr tr (by simp) rfl
    exact Or.inr (Or.inr (Or.inr ⟨result, targetValue, sourceNext, targetNext, a, b, r1, r2, remaining,
      eqs.1, eqs.2, ffi, bound, locations, after⟩))

/-- With no remaining clock, a successfully resolved direct tail call times
out on both sides with the same FFI and stack-maximum bound. -/
theorem tailCall64_direct_timeout {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names : List Nat) (values : List DataSem.Value) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (zeroClock : source.clock = 0) : timesOut64 conf secn label (.call none (some callee) names none) source target := by
  obtain ⟨words, wordRun, lengths⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  have zero : WordSemStateFiniteExact.getVar 0 target = some (.loc l1 l2) := related.2.2.2.2.2.2.2.2.2.2.1 rfl
  have allWords : WordSemStateFiniteExact.getVars (0 :: names.map adjustVar) target = some (.loc l1 l2 :: words) := by
    simp [WordSemStateFiniteExact.getVars, zero, wordRun]
  have code := stateRel64_findCode_direct conf l1 l2 source target locs related l1 l2 callee values words body size lengths found
  have targetZero : target.clock = 0 := by simpa [related.2.1] using zeroClock
  refine ⟨DataSem.flushState true source, WordSemStateFiniteExact.flushState true target, ?_, ?_, related.1, ?_⟩
  · simp [DataSem.evaluate, sourceRun, found, zeroClock]
  · have compiled : (compileControl64 conf secn label (.call none (some callee) names none)).1 =
        .call none (some callee) (0 :: names.map adjustVar) none := rfl
    rw [compiled]
    simp [WordSemStateFiniteExact.evaluate, allWords, wordSemBadDestArgs, wordSemAddRetLoc, code, targetZero]
  · exact related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Every source-safe direct tail call is simulated if its selected callee
satisfies the recursive simulation hypothesis. -/
theorem tailCall64_direct_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names : List Nat)
    (safe : (DataSem.evaluate (.call none (some callee) names none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (body : DataLang.Prog) (args : List DataSem.Value) (frameSize : Option Nat),
      DataSem.findCode (some callee) args source.code source.stackFrameSizes = some (args, body, frameSize) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
        outcomes64 conf callee 2 l1 l2 body s t locs) :
    outcomes64 conf secn label l1 l2 (.call none (some callee) names none) source target locs := by
  cases sourceRun : DataSem.getVars names source.locals with
  | none => simp [DataSem.evaluate, sourceRun] at safe
  | some values =>
    cases found : DataSem.findCode (some callee) values source.code source.stackFrameSizes with
    | none => simp [DataSem.evaluate, sourceRun, found] at safe
    | some info =>
      obtain ⟨args, body, size⟩ := info
      have argsEq : args = values := by
        unfold DataSem.findCode at found
        cases lookup : sptLookup callee source.code with
        | none => simp [lookup] at found
        | some entry =>
          obtain ⟨arity, prog⟩ := entry
          split at found <;> simp_all
      subst args
      by_cases zero : source.clock = 0
      · exact Or.inr (Or.inr (Or.inl (tailCall64_direct_timeout conf secn label l1 l2 source target locs related
          callee names values body size sourceRun found zero)))
      · exact tailCall64_direct_outcomes conf secn label l1 l2 source target locs related
          callee names values body size sourceRun found zero safe (calleeCorrect body values size found)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
