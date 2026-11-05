import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorIndirectCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectHandlerCallSpace

/-! Source-space-safe calls with local handlers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A caught direct call transfers the safety condition to its handler. -/
theorem caughtCall64_direct_outcomesWithSpace_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body handlerBody : DataLang.Prog)
    (handlerName : Nat) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0)
    (safe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source).2.safeForSpace = true)
    (calleeRaises : raises64 conf callee 2 body
      (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
          (WordSemStateFiniteExact.decClock target))) ((l1, l2) :: locs))
    (calleeCode : (DataSem.evaluate body
      (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))).2.code = source.code)
    (handlerCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock →
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate handlerBody s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate handlerBody s).2.safeForSpace = true →
      outcomesWithSpace64 conf secn (label + 2) l1 l2 handlerBody s t locs) :
    outcomesWithSpace64 conf secn label l1 l2 (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source target locs := by
  obtain ⟨value, word, sourceLast, targetLast, a, b, r1, r2, remaining, sourceBody, wordBody,
    ⟨jumpState, jump⟩, ffi, bound, locations, after⟩ := calleeRaises
  let sourceEntry := DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
      (WordSemStateFiniteExact.decClock target))
  have expectedJump := pushCall_jumpExc_destination target (sptInter target.locals (.ls ()))
    (sptInter target.locals (adjustSet live)) (.loc secn label :: args) size (adjustVar handlerName) secn (label + 1)
    (compileControl64 conf secn (label + 2) handlerBody).1
  change WordSemStateFiniteExact.jumpExc targetEntry = some (jumpState, a, b) at jump
  change ∃ next, WordSemStateFiniteExact.jumpExc targetEntry = some (next, secn, label + 1) at expectedJump
  obtain ⟨expectedState, expected⟩ := expectedJump
  rw [jump] at expected
  simp only [Option.some.injEq, Prod.mk.injEq] at expected
  have aEq : a = secn := expected.2.1
  have bEq : b = label + 1 := expected.2.2
  subst a
  subst b
  have stackFacts := evaluate_exception_caller_stack (compileControl64 conf callee 2 body).1
    (compileControl64 conf secn (label + 2) handlerBody).1 target (sptInter target.locals (.ls ()))
    (sptInter target.locals (adjustSet live)) (.loc secn label :: args) size (adjustVar handlerName) secn (label + 1)
    (.loc secn (label + 1)) word targetLast wordBody
  have sourceTargetLength := (after 0).2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  change sourceLast.stack.length = targetLast.stack.length at sourceTargetLength
  have targetLength := WordSemStackEq.sKeyEqLength _ _ stackFacts.1
  have locationLength := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  have sourceLength : sourceLast.stack.length = locs.length := by omega
  have locationEq : (l1, l2) :: locs = (r1, r2) :: remaining := by
    simpa [wordSemLastN_eq_drop, sourceLength] using locations
  simp only [List.cons.injEq, Prod.mk.injEq] at locationEq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := locationEq
  let k := min sourceEntry.clock sourceLast.clock
  let sourceClamped := { sourceLast with clock := k }
  let targetClamped := { targetLast with clock := k, termdep := targetEntry.termdep }
  let handlerSource := DataSem.setVar handlerName value sourceClamped
  let handlerTarget := WordSemStateFiniteExact.setVar (adjustVar handlerName) word targetClamped
  have handlerRelated : stateRel64 conf l1 l2 handlerSource handlerTarget none locs :=
    stateRel64_withClock conf l1 l2 (DataSem.setVar handlerName value sourceLast)
      (WordSemStateFiniteExact.setVar (adjustVar handlerName) word targetLast) none locs k (after handlerName)
  have entryRelated := stateRel64_pushCall conf l1 l2 secn label source target locs related names values args size
    sourceRun wordRun live saved cut
      (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
  have entryClock : targetEntry.clock = sourceEntry.clock := entryRelated.2.1
  have afterClock : targetLast.clock = sourceLast.clock := (after 0).2.1
  have wordFix : WordSemStateFiniteExact.fixClock targetEntry
      (WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry) =
        (some (.exception (.loc secn (label + 1)) word), targetClamped) := by
    have minEq : (if sourceEntry.clock < sourceLast.clock then sourceEntry.clock else sourceLast.clock) = k := by
      dsimp [k]
      split <;> omega
    change WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry =
      (some (.exception (.loc secn (label + 1)) word), targetLast) at wordBody
    rw [wordBody]
    simp only [WordSemStateFiniteExact.fixClock, entryClock, afterClock, minEq, targetClamped]
  have domain := evaluate_fixClock_exception_domain (compileControl64 conf callee 2 body).1
    (compileControl64 conf secn (label + 2) handlerBody).1 target (sptInter target.locals (.ls ()))
    (sptInter target.locals (adjustSet live)) (.loc secn label :: args) size (adjustVar handlerName) secn (label + 1)
    (.loc secn (label + 1)) word targetClamped wordFix
  obtain ⟨wordCode, wordCut, notEmpty, mappedDistinct⟩ :=
    returningCall64_direct_setup conf secn label l1 l2 source target locs related callee names returns live saved values args body size
      sourceRun wordRun found cut distinct
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  have sourceEq : DataSem.evaluate (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source =
      DataSem.evaluate handlerBody handlerSource := by
    simp [DataSem.evaluate, sourceRun, found, distinct, cut, positive, sourceBody, DataSem.fixClock, handlerSource, sourceClamped, k, sourceEntry]
  have targetEq : WordSemStateFiniteExact.evaluate
      (compileControl64 conf secn label (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody)))).1 target =
      WordSemStateFiniteExact.evaluate (compileControl64 conf secn (label + 2) handlerBody).1 handlerTarget := by
    have compiled : (compileControl64 conf secn label
        (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody)))).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) (some callee) (names.map adjustVar)
          (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1)) := by
      conv_lhs => unfold compileControl64
      simp only [compileControl?]
      rw [compileControl64_checked conf secn (label + 2) handlerBody]
      rfl
    rw [compiled]
    simp only [adjustSets] at wordCut
    dsimp [targetEntry] at wordFix
    simp only [WordSemStateFiniteExact.evaluate, wordRun, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive]
    rw [wordFix]
    simp [domain, handlerTarget]
  have handlerSafe : (DataSem.evaluate handlerBody handlerSource).1 ≠ some (.err (.abort .typeError)) := by
    simpa only [sourceEq] using safe
  have sourceCode : handlerSource.code = source.code := by
    simpa [handlerSource, sourceClamped, DataSem.setVar, sourceBody] using calleeCode
  have sourceClock : handlerSource.clock < source.clock := by
    simp [handlerSource, sourceClamped, DataSem.setVar, k, sourceEntry, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
    omega
  have handlerSpace : (DataSem.evaluate handlerBody handlerSource).2.safeForSpace = true := by
    simpa only [sourceEq] using spaceSafe
  rcases handlerCorrect handlerSource handlerTarget sourceCode sourceClock handlerRelated handlerSafe handlerSpace with ordinary | failure
  · left
    apply outcomes64_of_evaluations conf secn label (label + 2) l1 l2 _ handlerBody source handlerSource target handlerTarget locs sourceEq targetEq
    · intro x y next jumpHandler
      apply jumpExc_destination_of_keyEq target handlerTarget next x y
      · exact stackFacts.1
      · exact stackFacts.2
      · exact jumpHandler
    · exact ordinary
  · right
    obtain ⟨final, run, bound, events, unsafeProof⟩ := failure
    exact ⟨final, targetEq.trans run, by simpa [sourceEq] using bound,
      by simpa [sourceEq] using events, by simpa [sourceEq] using unsafeProof⟩

/-- A direct returning call with a handler inherits ordinary or allocation
failure outcomes from both the callee and the caught-exception handler. -/
theorem call64_direct_handler_outcomesWithSpace_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body handlerBody : DataLang.Prog)
    (handlerName : Nat) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup)
    (safe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) → (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body s).2.safeForSpace = true →
      outcomesWithSpace64 conf callee 2 secn label body s t ((l1, l2) :: locs))
    (calleeCode : (DataSem.evaluate body
      (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))).2.code = source.code)
    (handlerCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock →
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate handlerBody s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate handlerBody s).2.safeForSpace = true →
      outcomesWithSpace64 conf secn (label + 2) l1 l2 handlerBody s t locs) :
    outcomesWithSpace64 conf secn label l1 l2 (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source target locs := by
  by_cases zero : source.clock = 0
  · exact Or.inl (Or.inr (Or.inr (Or.inl (returningCall64_direct_handler_zero_timeout conf secn label l1 l2 source target locs related
      callee names returns live saved values args body handlerBody handlerName size sourceRun wordRun found cut distinct zero))))
  · have entryRelated := stateRel64_pushCall conf l1 l2 secn label source target locs related names values args size
      sourceRun wordRun live saved cut
        (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
    have calleeSafe : (DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))).1 ≠
        some (.err (.abort .typeError)) := by
      intro bad
      cases run : DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))) with
      | mk result state =>
        have eq : result = some (.err (.abort .typeError)) := by simpa [run] using bad
        subst result
        simp [DataSem.evaluate, sourceRun, found, distinct, cut, zero, run, DataSem.fixClock] at safe
    have calleeSpace := (returningCall64_handler_sourceResource source callee names returns live saved values body handlerBody handlerName size
      sourceRun found cut distinct zero).2.2 spaceSafe
    rcases calleeCorrect (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))) _ rfl
        (by simp [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]; omega) entryRelated calleeSafe calleeSpace with ordinary | failure
    · rcases ordinary with continued | returned | timeout | raised
      · obtain ⟨sourceLast, targetLast, sr, tr, after⟩ := continued
        simp only [DataSem.evaluate, sourceRun, found, distinct, cut, zero, ↓reduceIte, Option.isSome_some] at safe
        rw [sr] at safe
        simp [DataSem.fixClock] at safe
      · exact Or.inl (Or.inl (returningCall64_direct_handler_of_safe conf secn label l1 l2 source target locs related
          callee names returns live saved values args body handlerBody handlerName size sourceRun wordRun found cut distinct zero safe returned))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (returningCall64_direct_handler_callee_timeout conf secn label l1 l2 source target locs related
          callee names returns live saved values args body handlerBody handlerName size sourceRun wordRun found cut distinct zero timeout))))
      · exact caughtCall64_direct_outcomesWithSpace_safe conf secn label l1 l2 source target locs related callee names returns live saved
          values args body handlerBody handlerName size sourceRun wordRun found cut distinct zero safe spaceSafe raised calleeCode handlerCorrect
    · exact Or.inr (returningCall64_direct_handler_outOfSpace conf secn label l1 l2 source target locs related
        callee names returns live saved values args body handlerBody handlerName size sourceRun wordRun found cut distinct zero failure)

/-- Source safety supplies direct-call setup for a call with a handler;
the callee and handler induction hypotheses admit allocation failure. -/
theorem call64_direct_handler_withSpace_and_spaceSafe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (handlerName : Nat) (handlerBody : DataLang.Prog)
    (safe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (body : DataLang.Prog) (args : List DataSem.Value) (size : Option Nat),
      DataSem.findCode (some callee) args source.code source.stackFrameSizes = some (args, body, size) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) → (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body s).2.safeForSpace = true →
        outcomesWithSpace64 conf callee 2 secn label body s t ((l1, l2) :: locs))
    (calleePreserves : ∀ (body : DataLang.Prog) (args : List DataSem.Value) (size : Option Nat) (saved : Spt DataSem.Value),
      DataSem.findCode (some callee) args source.code source.stackFrameSizes = some (args, body, size) →
      DataSem.cutEnv live source.locals = some saved →
      (DataSem.evaluate body (DataSem.callEnv args size (DataSem.pushEnv saved true (DataSem.decClock source)))).2.code = source.code)
    (handlerCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock →
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate handlerBody s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate handlerBody s).2.safeForSpace = true →
      outcomesWithSpace64 conf secn (label + 2) l1 l2 handlerBody s t locs) :
    outcomesWithSpace64 conf secn label l1 l2 (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source target locs := by
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
          exact call64_direct_handler_outcomesWithSpace_safe conf secn label l1 l2 source target locs related callee names returns live saved
            values words body handlerBody handlerName size sourceRun wordRun found cut distinct safe spaceSafe
            (calleeCorrect body values size found) (calleePreserves body values size saved found cut) handlerCorrect
      · simp [DataSem.evaluate, sourceRun, found, distinct] at safe

/-- A caught indirect call transfers source safety to its handler. -/
theorem caughtCall64_indirect_outcomesWithSpace_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (lastName : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body handlerBody : DataLang.Prog)
    (handlerName : Nat) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (pointer : DataSem.getVar lastName source.locals = some (.codePtr callee))
    (lookup : sptLookup callee source.code = some (values.length, body))
    (sizeEq : size = sptLookup callee source.stackFrameSizes)
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0)
    (safe : (DataSem.evaluate (.call (some (returns, live)) none (names ++ [lastName]) (some (handlerName, handlerBody))) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call (some (returns, live)) none (names ++ [lastName]) (some (handlerName, handlerBody))) source).2.safeForSpace = true)
    (calleeRaises : raises64 conf callee 2 body
      (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
          (WordSemStateFiniteExact.decClock target))) ((l1, l2) :: locs))
    (calleeCode : (DataSem.evaluate body
      (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))).2.code = source.code)
    (handlerCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock →
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate handlerBody s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate handlerBody s).2.safeForSpace = true →
      outcomesWithSpace64 conf secn (label + 2) l1 l2 handlerBody s t locs) :
    outcomesWithSpace64 conf secn label l1 l2 (.call (some (returns, live)) none (names ++ [lastName]) (some (handlerName, handlerBody))) source target locs := by
  obtain ⟨value, word, sourceLast, targetLast, a, b, r1, r2, remaining, sourceBody, wordBody,
    ⟨jumpState, jump⟩, ffi, bound, locations, after⟩ := calleeRaises
  let sourceEntry := DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
      (WordSemStateFiniteExact.decClock target))
  have expectedJump := pushCall_jumpExc_destination target (sptInter target.locals (.ls ()))
    (sptInter target.locals (adjustSet live)) (.loc secn label :: args) size (adjustVar handlerName) secn (label + 1)
    (compileControl64 conf secn (label + 2) handlerBody).1
  change WordSemStateFiniteExact.jumpExc targetEntry = some (jumpState, a, b) at jump
  change ∃ next, WordSemStateFiniteExact.jumpExc targetEntry = some (next, secn, label + 1) at expectedJump
  obtain ⟨expectedState, expected⟩ := expectedJump
  rw [jump] at expected
  simp only [Option.some.injEq, Prod.mk.injEq] at expected
  have aEq : a = secn := expected.2.1
  have bEq : b = label + 1 := expected.2.2
  subst a
  subst b
  have stackFacts := evaluate_exception_caller_stack (compileControl64 conf callee 2 body).1
    (compileControl64 conf secn (label + 2) handlerBody).1 target (sptInter target.locals (.ls ()))
    (sptInter target.locals (adjustSet live)) (.loc secn label :: args) size (adjustVar handlerName) secn (label + 1)
    (.loc secn (label + 1)) word targetLast wordBody
  have sourceTargetLength := (after 0).2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  change sourceLast.stack.length = targetLast.stack.length at sourceTargetLength
  have targetLength := WordSemStackEq.sKeyEqLength _ _ stackFacts.1
  have locationLength := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  have sourceLength : sourceLast.stack.length = locs.length := by omega
  have locationEq : (l1, l2) :: locs = (r1, r2) :: remaining := by
    simpa [wordSemLastN_eq_drop, sourceLength] using locations
  simp only [List.cons.injEq, Prod.mk.injEq] at locationEq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := locationEq
  let k := min sourceEntry.clock sourceLast.clock
  let sourceClamped := { sourceLast with clock := k }
  let targetClamped := { targetLast with clock := k, termdep := targetEntry.termdep }
  let handlerSource := DataSem.setVar handlerName value sourceClamped
  let handlerTarget := WordSemStateFiniteExact.setVar (adjustVar handlerName) word targetClamped
  have handlerRelated : stateRel64 conf l1 l2 handlerSource handlerTarget none locs :=
    stateRel64_withClock conf l1 l2 (DataSem.setVar handlerName value sourceLast)
      (WordSemStateFiniteExact.setVar (adjustVar handlerName) word targetLast) none locs k (after handlerName)
  have entryRelated := stateRel64_pushCall conf l1 l2 secn label source target locs related names values args size
    sourceRun wordRun live saved cut
      (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
  have entryClock : targetEntry.clock = sourceEntry.clock := entryRelated.2.1
  have afterClock : targetLast.clock = sourceLast.clock := (after 0).2.1
  have wordFix : WordSemStateFiniteExact.fixClock targetEntry
      (WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry) =
        (some (.exception (.loc secn (label + 1)) word), targetClamped) := by
    have minEq : (if sourceEntry.clock < sourceLast.clock then sourceEntry.clock else sourceLast.clock) = k := by
      dsimp [k]
      split <;> omega
    change WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry =
      (some (.exception (.loc secn (label + 1)) word), targetLast) at wordBody
    rw [wordBody]
    simp only [WordSemStateFiniteExact.fixClock, entryClock, afterClock, minEq, targetClamped]
  have domain := evaluate_fixClock_exception_domain (compileControl64 conf callee 2 body).1
    (compileControl64 conf secn (label + 2) handlerBody).1 target (sptInter target.locals (.ls ()))
    (sptInter target.locals (adjustSet live)) (.loc secn label :: args) size (adjustVar handlerName) secn (label + 1)
    (.loc secn (label + 1)) word targetClamped wordFix
  obtain ⟨sourceAll, wordAll, sourceCode, wordCode, wordCut, notEmpty, mappedDistinct, _⟩ :=
    indirectCall64_setup conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body
      sourceRun wordRun pointer lookup cut distinct
        (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
  have sourceCode' : DataSem.findCode none (values ++ [.codePtr callee]) source.code source.stackFrameSizes = some (values, body, size) := by
    simpa [sizeEq] using sourceCode
  have wordCode' : wordSemFindCode none ((.loc secn label :: args) ++ [.loc callee 0]) target.code target.stackSize =
      some (.loc secn label :: args, (compileControl64 conf callee 2 body).1, size) := by
    simpa [sizeEq] using wordCode
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  have sourceEq : DataSem.evaluate (.call (some (returns, live)) none (names ++ [lastName]) (some (handlerName, handlerBody))) source =
      DataSem.evaluate handlerBody handlerSource := by
    simp [DataSem.evaluate, sourceAll, sourceCode', distinct, cut, positive, sourceBody, DataSem.fixClock, handlerSource, sourceClamped, k, sourceEntry]
  have targetEq : WordSemStateFiniteExact.evaluate
      (compileControl64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) (some (handlerName, handlerBody)))).1 target =
      WordSemStateFiniteExact.evaluate (compileControl64 conf secn (label + 2) handlerBody).1 handlerTarget := by
    have compiled : (compileControl64 conf secn label
        (.call (some (returns, live)) none (names ++ [lastName]) (some (handlerName, handlerBody)))).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) none ((names ++ [lastName]).map adjustVar)
          (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1)) := by
      conv_lhs => unfold compileControl64
      simp only [compileControl?]
      rw [compileControl64_checked conf secn (label + 2) handlerBody]
      rfl
    rw [compiled]
    simp only [List.map_append, List.map_cons, List.map_nil] at wordAll
    simp only [List.cons_append] at wordCode'
    simp only [adjustSets] at wordCut
    dsimp [targetEntry] at wordFix
    simp only [WordSemStateFiniteExact.evaluate, wordAll, wordSemBadDestArgs, wordSemAddRetLoc, wordCode',
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive, List.map_append, List.map_cons, List.map_nil]
    rw [wordFix]
    simp [domain, handlerTarget]
  have handlerSafe : (DataSem.evaluate handlerBody handlerSource).1 ≠ some (.err (.abort .typeError)) := by
    simpa only [sourceEq] using safe
  have sourceCode : handlerSource.code = source.code := by
    simpa [handlerSource, sourceClamped, DataSem.setVar, sourceBody] using calleeCode
  have sourceClock : handlerSource.clock < source.clock := by
    simp [handlerSource, sourceClamped, DataSem.setVar, k, sourceEntry, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
    omega
  have handlerSpace : (DataSem.evaluate handlerBody handlerSource).2.safeForSpace = true := by
    simpa only [sourceEq] using spaceSafe
  rcases handlerCorrect handlerSource handlerTarget sourceCode sourceClock handlerRelated handlerSafe handlerSpace with ordinary | failure
  · left
    apply outcomes64_of_evaluations conf secn label (label + 2) l1 l2 _ handlerBody source handlerSource target handlerTarget locs sourceEq targetEq
    · intro x y next jumpHandler
      apply jumpExc_destination_of_keyEq target handlerTarget next x y
      · exact stackFacts.1
      · exact stackFacts.2
      · exact jumpHandler
    · exact ordinary
  · right
    obtain ⟨final, run, bound, events, unsafeProof⟩ := failure
    exact ⟨final, targetEq.trans run, by simpa [sourceEq] using bound,
      by simpa [sourceEq] using events, by simpa [sourceEq] using unsafeProof⟩

/-- Source-safe handled indirect calls compose with allocation-aware callee
and handler simulations. -/
theorem call64_indirect_handler_outcomesWithSpace_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (lastName : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body handlerBody : DataLang.Prog) (handlerName : Nat) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (pointer : DataSem.getVar lastName source.locals = some (.codePtr callee))
    (lookup : sptLookup callee source.code = some (values.length, body))
    (sizeEq : size = sptLookup callee source.stackFrameSizes)
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup)
    (safe : (DataSem.evaluate (.call (some (returns, live)) none (names ++ [lastName]) (some (handlerName, handlerBody))) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call (some (returns, live)) none (names ++ [lastName]) (some (handlerName, handlerBody))) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) → (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body s).2.safeForSpace = true →
      outcomesWithSpace64 conf callee 2 secn label body s t ((l1, l2) :: locs))
    (calleeCode : (DataSem.evaluate body
      (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))).2.code = source.code)
    (handlerCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock →
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate handlerBody s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate handlerBody s).2.safeForSpace = true →
      outcomesWithSpace64 conf secn (label + 2) l1 l2 handlerBody s t locs) :
    outcomesWithSpace64 conf secn label l1 l2 (.call (some (returns, live)) none (names ++ [lastName]) (some (handlerName, handlerBody))) source target locs := by
  obtain ⟨sourceAll, _, sourceCode, _, _, _, _, entryRelated⟩ :=
    indirectCall64_setup conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body
      sourceRun wordRun pointer lookup cut distinct
        (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
  have sourceCode' : DataSem.findCode none (values ++ [.codePtr callee]) source.code source.stackFrameSizes = some (values, body, size) := by
    simpa [sizeEq] using sourceCode
  by_cases zero : source.clock = 0
  · exact Or.inl (Or.inr (Or.inr (Or.inl (returningCall64_indirect_handler_zero_timeout conf secn label l1 l2 source target locs related
      callee names returns lastName live saved values args body handlerBody handlerName size sourceRun wordRun pointer lookup sizeEq cut distinct zero))))
  · have entryRelated' : stateRel64 conf secn label
        (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))
        (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
          (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
            (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
            (WordSemStateFiniteExact.decClock target))) none ((l1, l2) :: locs) := by
      simpa [sizeEq] using entryRelated
    have calleeSafe : (DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))).1 ≠
        some (.err (.abort .typeError)) := by
      intro bad
      cases run : DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))) with
      | mk result state =>
        have eq : result = some (.err (.abort .typeError)) := by simpa [run] using bad
        subst result
        simp [DataSem.evaluate, sourceAll, sourceCode', distinct, cut, zero, run, DataSem.fixClock] at safe
    have calleeSpace := (returningCall64_indirect_handler_sourceResource source callee names returns lastName live saved values body handlerBody handlerName size
      sourceAll sourceCode' cut distinct zero).2.2 spaceSafe
    rcases calleeCorrect (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))) _ rfl
        (by simp [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]; omega) entryRelated' calleeSafe calleeSpace with ordinary | failure
    · rcases ordinary with continued | returned | timeout | raised
      · obtain ⟨sourceLast, targetLast, sr, tr, after⟩ := continued
        simp only [DataSem.evaluate, sourceAll, sourceCode', distinct, cut, zero, ↓reduceIte, Option.isSome_some] at safe
        rw [sr] at safe
        simp [DataSem.fixClock] at safe
      · exact Or.inl (Or.inl (returningCall64_indirect_handler_of_safe conf secn label l1 l2 source target locs related
          callee names returns lastName live saved values args body handlerBody handlerName size sourceRun wordRun pointer lookup sizeEq cut distinct zero safe returned))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (returningCall64_indirect_handler_callee_timeout conf secn label l1 l2 source target locs related
          callee names returns lastName live saved values args body handlerBody handlerName size sourceRun wordRun pointer lookup sizeEq cut distinct zero timeout))))
      · exact caughtCall64_indirect_outcomesWithSpace_safe conf secn label l1 l2 source target locs related
          callee names returns lastName live saved values args body handlerBody handlerName size sourceRun wordRun pointer lookup sizeEq cut distinct zero safe spaceSafe raised calleeCode handlerCorrect
    · exact Or.inr (returningCall64_indirect_handler_outOfSpace conf secn label l1 l2 source target locs related
        callee names returns lastName live saved values args body handlerBody handlerName size sourceRun wordRun pointer lookup sizeEq cut distinct zero failure)

/-- A safe indirect call is simulated when its selected body satisfies the
recursive simulation hypothesis. -/
theorem call64_indirect_handler_withSpace_and_spaceSafe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names returns : List Nat) (live : NumSet) (handlerName : Nat) (handlerBody : DataLang.Prog)
    (safe : (DataSem.evaluate (.call (some (returns, live)) none names (some (handlerName, handlerBody))) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call (some (returns, live)) none names (some (handlerName, handlerBody))) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (callee arity : Nat) (body : DataLang.Prog),
      sptLookup callee source.code = some (arity, body) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) →
        (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body s).2.safeForSpace = true →
        outcomesWithSpace64 conf callee 2 secn label body s t ((l1, l2) :: locs))
    (calleePreserves : ∀ (callee arity : Nat) (body : DataLang.Prog) (values : List DataSem.Value) (saved : Spt DataSem.Value),
      sptLookup callee source.code = some (arity, body) → DataSem.cutEnv live source.locals = some saved →
      (DataSem.evaluate body (DataSem.callEnv values (sptLookup callee source.stackFrameSizes)
        (DataSem.pushEnv saved true (DataSem.decClock source)))).2.code = source.code)
    (handlerCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock →
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate handlerBody s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate handlerBody s).2.safeForSpace = true →
      outcomesWithSpace64 conf secn (label + 2) l1 l2 handlerBody s t locs) :
    outcomesWithSpace64 conf secn label l1 l2 (.call (some (returns, live)) none names (some (handlerName, handlerBody))) source target locs := by
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
                exact call64_indirect_handler_outcomesWithSpace_safe conf secn label l1 l2 source target locs related callee names returns name live saved
                  values words body handlerBody handlerName _ prefixRun wordRun finalRun lookup rfl cut distinct safe spaceSafe (calleeCorrect callee values.length body lookup) (calleePreserves callee values.length body values saved lookup cut) handlerCorrect
            · simp [DataSem.evaluate, run, found, distinct] at safe
          · simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc, lookup, length] at safe

/-- Constructor-aware fragments with direct, indirect, and handled calls. -/
inductive HandledConstructorFragment : DataLang.Prog → Prop where
  | base {program : DataLang.Prog} : VerifiedWithConstructors program → HandledConstructorFragment program
  | seq {first second : DataLang.Prog} : HandledConstructorFragment first → HandledConstructorFragment second →
      HandledConstructorFragment (.seq first second)
  | ite (name : Nat) {yes no : DataLang.Prog} : HandledConstructorFragment yes → HandledConstructorFragment no →
      HandledConstructorFragment (.ifThenElse name yes no)
  | tailCall (callee : Nat) (names : List Nat) : HandledConstructorFragment (.call none (some callee) names none)
  | returningCall (callee : Nat) (names returns : List Nat) (live : NumSet) :
      HandledConstructorFragment (.call (some (returns, live)) (some callee) names none)
  | indirectTailCall (names : List Nat) : HandledConstructorFragment (.call none none names none)
  | indirectReturningCall (names returns : List Nat) (live : NumSet) :
      HandledConstructorFragment (.call (some (returns, live)) none names none)
  | handledCall (callee : Nat) (names returns : List Nat) (live : NumSet) (handlerName : Nat)
      {handlerBody : DataLang.Prog} : HandledConstructorFragment handlerBody →
      HandledConstructorFragment (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody)))
  | indirectHandledCall (names returns : List Nat) (live : NumSet) (handlerName : Nat)
      {handlerBody : DataLang.Prog} : HandledConstructorFragment handlerBody →
      HandledConstructorFragment (.call (some (returns, live)) none names (some (handlerName, handlerBody)))

/-- Each callable body belongs to the handled-call constructor fragment. -/
def HandledConstructorFragmentCode (code : Spt (Nat × DataLang.Prog)) : Prop :=
  ∀ label arity body, sptLookup label code = some (arity, body) → HandledConstructorFragment body

/-- The fragment preserves source code across recursive calls. -/
theorem handledConstructorFragment_code {C F : Type} (program : DataLang.Prog)
    (fragment : HandledConstructorFragment program) (state : DataSem.State C F)
    (closed : HandledConstructorFragmentCode state.code) : (DataSem.evaluate program state).2.code = state.code := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), HandledConstructorFragment program →
      ∀ state : DataSem.State C F, state.clock = clock → HandledConstructorFragmentCode state.code →
        (DataSem.evaluate program state).2.code = state.code := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro program fragment
      induction fragment with
      | base frag => intro state _ _; exact verifiedWithConstructors_code _ frag state
      | @seq first second firstFrag secondFrag firstIH secondIH =>
        intro state eq closed
        apply DataSem.evaluate_seq_code_step first second state (firstIH state eq closed)
        intro mid codeEq clockBound
        have midClosed : HandledConstructorFragmentCode mid.code := by simpa [codeEq] using closed
        rcases Nat.lt_or_eq_of_le clockBound with less | equal
        · exact clockIH mid.clock (by omega) second secondFrag mid rfl midClosed
        · exact secondIH mid (by omega) midClosed
      | @ite name yes no yesFrag noFrag yesIH noIH =>
        intro state eq closed
        exact DataSem.evaluate_if_code_step name yes no state (yesIH state eq closed) (noIH state eq closed)
      | tailCall callee names =>
        intro state eq closed
        apply DataSem.evaluate_call_code_step none (some callee) names none state
        · intro values args body size found next smaller codeEq
          obtain ⟨label, arity, lookup⟩ := findCode_body_lookup (some callee) values state.code
            state.stackFrameSizes args body size found
          have member := closed label arity body lookup
          have nextClosed : HandledConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq
          cases handlerEq
      | returningCall callee names returns live =>
        intro state eq closed
        apply DataSem.evaluate_call_code_step (some (returns, live)) (some callee) names none state
        · intro values args body size found next smaller codeEq
          obtain ⟨label, arity, lookup⟩ := findCode_body_lookup (some callee) values state.code
            state.stackFrameSizes args body size found
          have member := closed label arity body lookup
          have nextClosed : HandledConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq
          cases handlerEq
      | indirectTailCall names =>
        intro state eq closed
        apply DataSem.evaluate_call_code_step none none names none state
        · intro values args body size found next smaller codeEq
          obtain ⟨label, arity, lookup⟩ := findCode_body_lookup none values state.code
            state.stackFrameSizes args body size found
          have member := closed label arity body lookup
          have nextClosed : HandledConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq
          cases handlerEq
      | indirectReturningCall names returns live =>
        intro state eq closed
        apply DataSem.evaluate_call_code_step (some (returns, live)) none names none state
        · intro values args body size found next smaller codeEq
          obtain ⟨label, arity, lookup⟩ := findCode_body_lookup none values state.code
            state.stackFrameSizes args body size found
          have member := closed label arity body lookup
          have nextClosed : HandledConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq
          cases handlerEq
      | @handledCall callee names returns live handlerName handlerBody handlerFrag handlerIH =>
        intro state eq closed
        apply DataSem.evaluate_call_code_step (some (returns, live)) (some callee) names (some (handlerName, handlerBody)) state
        · intro values args body size found next smaller codeEq
          obtain ⟨label, arity, lookup⟩ := findCode_body_lookup (some callee) values state.code
            state.stackFrameSizes args body size found
          have member := closed label arity body lookup
          have nextClosed : HandledConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq next smaller codeEq
          cases handlerEq
          have nextClosed : HandledConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) handlerBody handlerFrag next rfl nextClosed).trans codeEq
      | @indirectHandledCall names returns live handlerName handlerBody handlerFrag handlerIH =>
        intro state eq closed
        apply DataSem.evaluate_call_code_step (some (returns, live)) none names (some (handlerName, handlerBody)) state
        · intro values args body size found next smaller codeEq
          obtain ⟨label, arity, lookup⟩ := findCode_body_lookup none values state.code
            state.stackFrameSizes args body size found
          have member := closed label arity body lookup
          have nextClosed : HandledConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq next smaller codeEq
          cases handlerEq
          have nextClosed : HandledConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) handlerBody handlerFrag next rfl nextClosed).trans codeEq
  exact allClocks state.clock program fragment state rfl closed

/-- Closed constructor-aware programs, including mutually recursive direct and
indirect calls, have an ordinary related outcome or permitted allocation failure.
This is a conditional Flapjack simulation, not unrestricted HOL correctness. -/
theorem handledConstructorFragment64 {C F : Type} (conf : Config) (program : DataLang.Prog)
    (fragment : HandledConstructorFragment program) :
    ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
      (locs : List (Nat × Nat)), HandledConstructorFragmentCode source.code →
      stateRel64 conf l1 l2 source target none locs →
      (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate program source).2.safeForSpace = true →
      outcomesWithSpace64 conf secn label l1 l2 program source target locs := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), HandledConstructorFragment program →
      ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
        (locs : List (Nat × Nat)), source.clock = clock → HandledConstructorFragmentCode source.code →
        stateRel64 conf l1 l2 source target none locs →
        (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
        (DataSem.evaluate program source).2.safeForSpace = true →
        outcomesWithSpace64 conf secn label l1 l2 program source target locs := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro program fragment
      induction fragment with
      | base frag =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
        exact verifiedWithConstructors64 conf secn l1 l2 _ frag label source target locs related safe spaceSafe
      | @seq first second firstFrag secondFrag firstIH secondIH =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
        have firstOutcome := firstIH secn label l1 l2 source target locs eq closed related
          (seq_first_safe first second source safe) (seq_first_space_safe first second source spaceSafe)
        have firstCode := handledConstructorFragment_code first firstFrag source closed
        apply seq64_outcomesWithSpace_safe_closed conf secn label l1 l2 first second source target locs related safe spaceSafe
          firstOutcome firstCode
        intro s t codeEq bound rel valid space
        have nextClosed : HandledConstructorFragmentCode s.code := by simpa [codeEq] using closed
        rcases Nat.lt_or_eq_of_le bound with less | same
        · exact clockIH s.clock (by omega) second secondFrag secn (compileControl64 conf secn label first).2
            l1 l2 s t locs rfl nextClosed rel valid space
        · exact secondIH secn (compileControl64 conf secn label first).2 l1 l2 s t locs (by omega) nextClosed rel valid space
      | @ite name yes no yesFrag noFrag yesIH noIH =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
        apply if64_outcomesWithSpace_safe conf secn label l1 l2 name yes no source target locs related safe spaceSafe
        · intro valid space
          exact yesIH secn label l1 l2 source target locs eq closed related valid space
        · intro valid space
          exact noIH secn (compileControl64 conf secn label yes).2 l1 l2 source target locs eq closed related valid space
      | tailCall callee names =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
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
            · exact Or.inl (Or.inr (Or.inr (Or.inl (tailCall64_direct_timeout conf secn label l1 l2 source target locs related
                callee names values body size sourceRun found zero))))
            · obtain ⟨arity, lookup⟩ := findCode_direct_body_lookup callee values source.code source.stackFrameSizes body size found
              have member := closed callee arity body lookup
              apply tailCall64_direct_withSpace_safe conf secn label l1 l2 source target locs related
                callee names values body size sourceRun found zero safe spaceSafe
              intro t rel valid space
              have nextClosed : HandledConstructorFragmentCode (DataSem.callEnv values size (DataSem.decClock source)).code := by
                simpa [DataSem.callEnv, DataSem.decClock] using closed
              exact clockIH (DataSem.callEnv values size (DataSem.decClock source)).clock (by
                simp [DataSem.callEnv, DataSem.decClock]
                omega) body member callee 2 l1 l2 (DataSem.callEnv values size (DataSem.decClock source)) t locs
                rfl nextClosed rel valid space
      | returningCall callee names returns live =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
        apply call64_direct_noHandler_withSpace_and_spaceSafe conf secn label l1 l2 source target locs related
          callee names returns live safe spaceSafe
        intro body args size found s t codeEq smaller rel valid space
        obtain ⟨calleeLabel, arity, lookup⟩ := findCode_body_lookup (some callee) args source.code
          source.stackFrameSizes args body size found
        have member := closed calleeLabel arity body lookup
        have nextClosed : HandledConstructorFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs)
          rfl nextClosed rel valid space
      | indirectTailCall names =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
        apply tailCall64_indirect_withSpace_and_spaceSafe conf secn label l1 l2 source target locs related names safe spaceSafe
        intro callee arity body lookup s t codeEq smaller rel valid space
        have member := closed callee arity body lookup
        have nextClosed : HandledConstructorFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 l1 l2 s t locs rfl nextClosed rel valid space
      | indirectReturningCall names returns live =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
        apply call64_indirect_noHandler_withSpace_and_spaceSafe conf secn label l1 l2 source target locs related
          names returns live safe spaceSafe
        intro callee arity body lookup s t codeEq smaller rel valid space
        have member := closed callee arity body lookup
        have nextClosed : HandledConstructorFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs)
          rfl nextClosed rel valid space
      | @handledCall callee names returns live handlerName handlerBody handlerFrag handlerIH =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
        apply call64_direct_handler_withSpace_and_spaceSafe conf secn label l1 l2 source target locs related
          callee names returns live handlerName handlerBody safe spaceSafe
        · intro body args size found s t codeEq smaller rel valid space
          obtain ⟨calleeLabel, arity, lookup⟩ := findCode_body_lookup (some callee) args source.code
            source.stackFrameSizes args body size found
          have member := closed calleeLabel arity body lookup
          have nextClosed : HandledConstructorFragmentCode s.code := by simpa [codeEq] using closed
          exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs) rfl nextClosed rel valid space
        · intro body args size saved found cut
          obtain ⟨calleeLabel, arity, lookup⟩ := findCode_body_lookup (some callee) args source.code
            source.stackFrameSizes args body size found
          have member := closed calleeLabel arity body lookup
          simpa [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using
            handledConstructorFragment_code body member
              (DataSem.callEnv args size (DataSem.pushEnv saved true (DataSem.decClock source)))
              (by simpa [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using closed)
        · intro s t codeEq smaller rel valid space
          have nextClosed : HandledConstructorFragmentCode s.code := by simpa [codeEq] using closed
          exact clockIH s.clock (by omega) handlerBody handlerFrag secn (label + 2) l1 l2 s t locs rfl nextClosed rel valid space
      | @indirectHandledCall names returns live handlerName handlerBody handlerFrag handlerIH =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
        apply call64_indirect_handler_withSpace_and_spaceSafe conf secn label l1 l2 source target locs related
          names returns live handlerName handlerBody safe spaceSafe
        · intro callee arity body lookup s t codeEq smaller rel valid space
          have member := closed callee arity body lookup
          have nextClosed : HandledConstructorFragmentCode s.code := by simpa [codeEq] using closed
          exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs) rfl nextClosed rel valid space
        · intro callee arity body values saved lookup cut
          have member := closed callee arity body lookup
          simpa [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using
            handledConstructorFragment_code body member
              (DataSem.callEnv values (sptLookup callee source.stackFrameSizes)
                (DataSem.pushEnv saved true (DataSem.decClock source)))
              (by simpa [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using closed)
        · intro s t codeEq smaller rel valid space
          have nextClosed : HandledConstructorFragmentCode s.code := by simpa [codeEq] using closed
          exact clockIH s.clock (by omega) handlerBody handlerFrag secn (label + 2) l1 l2 s t locs rfl nextClosed rel valid space
  intro secn label l1 l2 source target locs closed related safe spaceSafe
  exact allClocks source.clock program fragment secn label l1 l2 source target locs rfl closed related safe spaceSafe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
