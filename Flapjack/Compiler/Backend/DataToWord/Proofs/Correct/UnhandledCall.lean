import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CallTimeout
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Fragment

/-! Propagation of exceptions through calls without local handlers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A callee exception propagates through a direct non-tail call to the same
outer handler, with the saved caller frame removed from the location list. -/
theorem unhandledCall64_direct {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0)
    (calleeRaises : raises64 conf callee 2 body
      (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          none (WordSemStateFiniteExact.decClock target))) ((l1, l2) :: locs)) :
    raises64 conf secn label (.call (some (returns, live)) (some callee) names none) source target locs := by
  obtain ⟨value, word, sourceLast, targetLast, a, b, r1, r2, remaining, sourceBody, wordBody,
    ⟨jumpState, jump⟩, ffi, bound, locations, after⟩ := calleeRaises
  let sourceEntry := DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      none (WordSemStateFiniteExact.decClock target))
  have outerJump := pushCall_noHandler_jumpExc_destination target jumpState (sptInter target.locals (.ls ()))
    (sptInter target.locals (adjustSet live)) (.loc secn label :: args) size a b jump
  obtain ⟨outerState, outerRun⟩ := outerJump
  have outerValid : target.handler < target.stack.length := by
    by_contra invalid
    simp [WordSemStateFiniteExact.jumpExc, invalid] at outerRun
  have shorter := evaluate_noHandler_exception_stack_shorter (compileControl64 conf callee 2 body).1 target targetLast
    (sptInter target.locals (.ls ())) (sptInter target.locals (adjustSet live)) (.loc secn label :: args) size
    (.loc a b) word wordBody outerValid
  have sourceTargetLength := (after 0).2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  change sourceLast.stack.length = targetLast.stack.length at sourceTargetLength
  have locationLength := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  have sourceShorter : sourceLast.stack.length < locs.length := by omega
  have sameSuffix : wordSemLastN (sourceLast.stack.length + 1) ((l1, l2) :: locs) =
      wordSemLastN (sourceLast.stack.length + 1) locs := by
    rw [wordSemLastN_eq_drop, wordSemLastN_eq_drop]
    simp only [List.length_cons]
    have difference : locs.length + 1 - (sourceLast.stack.length + 1) =
        (locs.length - (sourceLast.stack.length + 1)) + 1 := by omega
    rw [difference]
    rfl
  rw [sameSuffix] at locations
  let k := min sourceEntry.clock sourceLast.clock
  let sourceClamped := { sourceLast with clock := k }
  let targetClamped := { targetLast with clock := k, termdep := targetEntry.termdep }
  have entryRelated := stateRel64_pushCall conf l1 l2 secn label source target locs related names values args size
    sourceRun wordRun live saved cut none
  have entryClock : targetEntry.clock = sourceEntry.clock := entryRelated.2.1
  have afterClock : targetLast.clock = sourceLast.clock := (after 0).2.1
  have wordFix : WordSemStateFiniteExact.fixClock targetEntry
      (WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry) =
        (some (.exception (.loc a b) word), targetClamped) := by
    have minEq : (if sourceEntry.clock < sourceLast.clock then sourceEntry.clock else sourceLast.clock) = k := by
      dsimp [k]
      split <;> omega
    change WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry =
      (some (.exception (.loc a b) word), targetLast) at wordBody
    rw [wordBody]
    simp only [WordSemStateFiniteExact.fixClock, entryClock, afterClock, minEq, targetClamped]
  obtain ⟨wordCode, wordCut, notEmpty, mappedDistinct⟩ :=
    returningCall64_direct_setup conf secn label l1 l2 source target locs related callee names returns live saved values args body size
      sourceRun wordRun found cut distinct
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  simp only [adjustSets] at wordCut
  dsimp [targetEntry] at wordFix
  refine ⟨value, word, sourceClamped, targetClamped, a, b, r1, r2, remaining, ?_, ?_, ⟨outerState, outerRun⟩,
    ffi, bound, locations, ?_⟩
  · simp [DataSem.evaluate, sourceRun, found, distinct, cut, positive, sourceBody,
      DataSem.fixClock, sourceClamped, k, sourceEntry]
  · have compiled : (compileControl64 conf secn label (.call (some (returns, live)) (some callee) names none)).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) (some callee) (names.map adjustVar) none := rfl
    rw [compiled]
    simp only [WordSemStateFiniteExact.evaluate, wordRun, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive]
    rw [wordFix]
    simp
  · intro dest
    exact stateRel64_withClock conf r1 r2 (DataSem.setVar dest value sourceLast)
      (WordSemStateFiniteExact.setVar (adjustVar dest) word targetLast) none remaining k (after dest)

/-- A source-safe direct call without a handler composes with its selected
callee's simulation for all currently covered outcomes. -/
theorem call64_direct_noHandler_outcomes {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup)
    (safe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf secn label s t none ((l1, l2) :: locs) → (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf callee 2 secn label body s t ((l1, l2) :: locs)) :
    outcomes64 conf secn label l1 l2 (.call (some (returns, live)) (some callee) names none) source target locs := by
  by_cases zero : source.clock = 0
  · exact Or.inr (Or.inr (Or.inl (returningCall64_direct_zero_timeout conf secn label l1 l2 source target locs related
      callee names returns live saved values args body size sourceRun wordRun found cut distinct zero)))
  · have entryRelated := stateRel64_pushCall conf l1 l2 secn label source target locs related names values args size
      sourceRun wordRun live saved cut none
    have calleeSafe : (DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))).1 ≠
        some (.err (.abort .typeError)) := by
      intro bad
      cases run : DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))) with
      | mk result state =>
        have eq : result = some (.err (.abort .typeError)) := by simpa [run] using bad
        subst result
        simp [DataSem.evaluate, sourceRun, found, distinct, cut, zero, run, DataSem.fixClock] at safe
    rcases calleeCorrect _ _ entryRelated calleeSafe with continued | returned | timeout | raised
    · obtain ⟨sourceLast, targetLast, sr, tr, after⟩ := continued
      simp only [Option.isSome_none] at sr
      simp only [DataSem.evaluate, sourceRun, found, distinct, cut, zero, ↓reduceIte, Option.isSome_none] at safe
      rw [sr] at safe
      simp [DataSem.fixClock] at safe
    · exact Or.inl (returningCall64_direct_of_safe conf secn label l1 l2 source target locs related
        callee names returns live saved values args body size sourceRun wordRun found cut distinct zero safe returned)
    · exact Or.inr (Or.inr (Or.inl (returningCall64_direct_callee_timeout conf secn label l1 l2 source target locs related
        callee names returns live saved values args body size sourceRun wordRun found cut distinct zero timeout)))
    · exact Or.inr (Or.inr (Or.inr (unhandledCall64_direct conf secn label l1 l2 source target locs related
        callee names returns live saved values args body size sourceRun wordRun found cut distinct zero raised)))

/-- Source safety supplies the successful direct-call setup, leaving only the
recursive simulation of the selected callee. -/
theorem call64_direct_noHandler_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet)
    (safe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (body : DataLang.Prog) (args : List DataSem.Value) (size : Option Nat),
      DataSem.findCode (some callee) args source.code source.stackFrameSizes = some (args, body, size) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        stateRel64 conf secn label s t none ((l1, l2) :: locs) → (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
        outcomes64 conf callee 2 secn label body s t ((l1, l2) :: locs)) :
    outcomes64 conf secn label l1 l2 (.call (some (returns, live)) (some callee) names none) source target locs := by
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
      by_cases distinct : returns.Nodup
      · cases cut : DataSem.cutEnv live source.locals with
        | none => simp [DataSem.evaluate, sourceRun, found, distinct, cut] at safe
        | some saved =>
          obtain ⟨words, wordRun, _⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
          exact call64_direct_noHandler_outcomes conf secn label l1 l2 source target locs related callee names returns live saved
            values words body size sourceRun wordRun found cut distinct safe (calleeCorrect body values size found)
      · simp [DataSem.evaluate, sourceRun, found, distinct] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
