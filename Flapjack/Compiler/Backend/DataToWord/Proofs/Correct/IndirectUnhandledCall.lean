import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.UnhandledCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectCallSetup
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectReturningCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectCallTimeout

/-! Propagation of exceptions through indirect returning calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A callee exception propagates through a indirect non-tail call to the same
outer handler, with the saved caller frame removed from the location list. -/
theorem unhandledCall64_indirect {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (lastName : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (pointer : DataSem.getVar lastName source.locals = some (.codePtr callee))
    (lookup : sptLookup callee source.code = some (values.length, body))
    (sizeEq : size = sptLookup callee source.stackFrameSizes)
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0)
    (calleeRaises : raises64 conf callee 2 body
      (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          none (WordSemStateFiniteExact.decClock target))) ((l1, l2) :: locs)) :
    raises64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) none) source target locs := by
  obtain ⟨value, word, sourceLast, targetLast, a, b, r1, r2, remaining, sourceBody, wordBody,
    ⟨jumpState, jump⟩, ffi, bound, locations, after⟩ := calleeRaises
  subst size
  obtain ⟨sourceAll, wordAll, sourceCode, wordCode, wordCut, notEmpty, mappedDistinct, entryRelated⟩ :=
    indirectCall64_setup conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body
      sourceRun wordRun pointer lookup cut distinct none
  let sourceEntry := DataSem.callEnv values (sptLookup callee source.stackFrameSizes) (DataSem.pushEnv saved false (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) (sptLookup callee source.stackFrameSizes)
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      none (WordSemStateFiniteExact.decClock target))
  have outerJump := pushCall_noHandler_jumpExc_destination target jumpState (sptInter target.locals (.ls ()))
    (sptInter target.locals (adjustSet live)) (.loc secn label :: args) (sptLookup callee source.stackFrameSizes) a b jump
  obtain ⟨outerState, outerRun⟩ := outerJump
  have outerValid : target.handler < target.stack.length := by
    by_contra invalid
    simp [WordSemStateFiniteExact.jumpExc, invalid] at outerRun
  have shorter := evaluate_noHandler_exception_stack_shorter (compileControl64 conf callee 2 body).1 target targetLast
    (sptInter target.locals (.ls ())) (sptInter target.locals (adjustSet live)) (.loc secn label :: args) (sptLookup callee source.stackFrameSizes)
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
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  simp only [adjustSets] at wordCut
  dsimp [targetEntry] at wordFix
  refine ⟨value, word, sourceClamped, targetClamped, a, b, r1, r2, remaining, ?_, ?_, ⟨outerState, outerRun⟩,
    ffi, bound, locations, ?_⟩
  · simp [DataSem.evaluate, sourceAll, sourceCode, distinct, cut, positive, sourceBody,
      DataSem.fixClock, sourceClamped, k, sourceEntry]
  · have compiled : (compileControl64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) none)).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) none ((names ++ [lastName]).map adjustVar) none := rfl
    rw [compiled]
    simp only [List.map_append, List.map_cons, List.map_nil] at wordAll
    simp only [List.cons_append] at wordCode
    simp only [WordSemStateFiniteExact.evaluate, wordAll, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive, List.map_append, List.map_cons, List.map_nil]
    rw [wordFix]
    simp
  · intro dest
    exact stateRel64_withClock conf r1 r2 (DataSem.setVar dest value sourceLast)
      (WordSemStateFiniteExact.setVar (adjustVar dest) word targetLast) none remaining k (after dest)

/-- A source-safe indirect call without a handler composes with its selected
callee's simulation for all currently covered outcomes. -/
theorem call64_indirect_noHandler_outcomes {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (lastName : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (pointer : DataSem.getVar lastName source.locals = some (.codePtr callee))
    (lookup : sptLookup callee source.code = some (values.length, body))
    (sizeEq : size = sptLookup callee source.stackFrameSizes)
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup)
    (safe : (DataSem.evaluate (.call (some (returns, live)) none (names ++ [lastName]) none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) → (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf callee 2 secn label body s t ((l1, l2) :: locs)) :
    outcomes64 conf secn label l1 l2 (.call (some (returns, live)) none (names ++ [lastName]) none) source target locs := by
  obtain ⟨sourceAll, _, sourceCode, _, _, _, _, entryRelated⟩ :=
    indirectCall64_setup conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body
      sourceRun wordRun pointer lookup cut distinct none
  have sourceCode' : DataSem.findCode none (values ++ [.codePtr callee]) source.code source.stackFrameSizes = some (values, body, size) := by
    simpa [sizeEq] using sourceCode
  by_cases zero : source.clock = 0
  · exact Or.inr (Or.inr (Or.inl (returningCall64_indirect_zero_timeout conf secn label l1 l2 source target locs related
      callee names returns lastName live saved values args body size sourceRun wordRun pointer lookup sizeEq cut distinct zero)))
  · have entryRelated' : stateRel64 conf secn label
        (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))
        (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
          (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) none
            (WordSemStateFiniteExact.decClock target))) none ((l1, l2) :: locs) := by
      simpa [sizeEq] using entryRelated
    have calleeSafe : (DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))).1 ≠
        some (.err (.abort .typeError)) := by
      intro bad
      cases run : DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))) with
      | mk result state =>
        have eq : result = some (.err (.abort .typeError)) := by simpa [run] using bad
        subst result
        simp [DataSem.evaluate, sourceAll, sourceCode', distinct, cut, zero, run, DataSem.fixClock] at safe
    rcases calleeCorrect (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))) _ rfl (by simp [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]; omega) entryRelated' calleeSafe with continued | returned | timeout | raised
    · obtain ⟨sourceLast, targetLast, sr, tr, after⟩ := continued
      simp only [DataSem.evaluate, sourceAll, sourceCode', distinct, cut, zero, ↓reduceIte, Option.isSome_none] at safe
      rw [sr] at safe
      simp [DataSem.fixClock] at safe
    · exact Or.inl (returningCall64_indirect_of_safe conf secn label l1 l2 source target locs related
        callee names returns lastName live saved values args body size sourceRun wordRun pointer lookup sizeEq cut distinct zero safe returned)
    · exact Or.inr (Or.inr (Or.inl (returningCall64_indirect_callee_timeout conf secn label l1 l2 source target locs related
        callee names returns lastName live saved values args body size sourceRun wordRun pointer lookup sizeEq cut distinct zero timeout)))
    · exact Or.inr (Or.inr (Or.inr (unhandledCall64_indirect conf secn label l1 l2 source target locs related
        callee names returns lastName live saved values args body size sourceRun wordRun pointer lookup sizeEq cut distinct zero raised)))

/-- A safe indirect call is simulated when its selected body satisfies the
recursive simulation hypothesis. -/
theorem call64_indirect_noHandler_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names returns : List Nat) (live : NumSet)
    (safe : (DataSem.evaluate (.call (some (returns, live)) none names none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (callee arity : Nat) (body : DataLang.Prog),
      sptLookup callee source.code = some (arity, body) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) →
        (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
        outcomes64 conf callee 2 secn label body s t ((l1, l2) :: locs)) :
    outcomes64 conf secn label l1 l2 (.call (some (returns, live)) none names none) source target locs := by
  induction names using List.reverseRecOn with
  | nil => simp [DataSem.evaluate, DataSem.getVars, DataSem.findCode] at safe
  | append_singleton names name ih =>
    cases run : DataSem.getVars (names ++ [name]) source.locals with
    | none => simp [DataSem.evaluate, run] at safe
    | some allValues =>
      obtain ⟨values, final, prefixRun, finalRun, equal⟩ := dataGetVars_unsnoc names name source.locals allValues run
      subst allValues
      cases final with
      | number n => simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc] at safe
      | word64 w => simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc] at safe
      | block stamp tag fields => simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc] at safe
      | refPtr immutable address => simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc] at safe
      | codePtr callee =>
        cases lookup : sptLookup callee source.code with
        | none => simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc, lookup] at safe
        | some entry =>
          obtain ⟨arity, body⟩ := entry
          by_cases length : values.length = arity
          · subst arity
            have found : DataSem.findCode none (values ++ [.codePtr callee]) source.code source.stackFrameSizes =
                some (values, body, sptLookup callee source.stackFrameSizes) := by
              simp [DataSem.findCode, holLast_snoc, lookup]
            by_cases distinct : returns.Nodup
            · cases cut : DataSem.cutEnv live source.locals with
              | none => simp [DataSem.evaluate, run, found, distinct, cut] at safe
              | some saved =>
                obtain ⟨words, wordRun, _⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values prefixRun
                exact call64_indirect_noHandler_outcomes conf secn label l1 l2 source target locs related callee names returns name live saved
                  values words body _ prefixRun wordRun finalRun lookup rfl cut distinct safe (calleeCorrect callee values.length body lookup)
            · simp [DataSem.evaluate, run, found, distinct] at safe
          · simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc, lookup, length] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
