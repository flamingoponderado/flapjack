import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ReturningCallSpace
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CaughtCall

/-! Allocation-failure propagation through calls with local handlers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A returning call with a local handler cannot decrease the callee's
resource observations. In the exception case this includes the handler's
actual evaluation, using source resource monotonicity. This is Flapjack
infrastructure for the data-to-word simulation. -/
theorem returningCall64_handler_sourceResource {C F : Type}
    (source : DataSem.State C F) (callee : Nat) (names returns : List Nat) (live : NumSet)
    (saved : Spt DataSem.Value) (values : List DataSem.Value) (body handlerBody : DataLang.Prog)
    (handlerName : Nat) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0) :
    DataSem.ResourceLe
      (DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))).2
      (DataSem.evaluate (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source).2 := by
  let entry := DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))
  cases bodyRun : DataSem.evaluate body entry with
  | mk result final =>
    let clamped := { final with clock := min entry.clock final.clock }
    cases result with
    | none =>
      simp [DataSem.evaluate, sourceRun, found, distinct, cut, positive, bodyRun, DataSem.fixClock,
        DataSem.ResourceLe, BackendProps.optionLe_refl, entry]
    | some result =>
      cases result with
      | err error =>
        cases error with
        | abort reason =>
          simp [DataSem.evaluate, sourceRun, found, distinct, cut, positive, bodyRun, DataSem.fixClock,
            DataSem.ResourceLe, BackendProps.optionLe_refl, entry]
        | raise value =>
          have monotone := DataSem.evaluate_resourceMono handlerBody (DataSem.setVar handlerName value clamped)
          simpa [DataSem.evaluate, sourceRun, found, distinct, cut, positive, bodyRun, DataSem.fixClock,
            DataSem.ResourceLe, DataSem.ResourceMono, DataSem.setVar, clamped, entry] using monotone
      | val returned =>
        by_cases arity : returned.length = returns.length
        · cases pop : DataSem.popEnv clamped with
          | none =>
            simp [DataSem.evaluate, sourceRun, found, distinct, cut, positive, bodyRun, DataSem.fixClock,
              arity, pop, clamped, DataSem.ResourceLe, BackendProps.optionLe_refl, entry]
          | some next =>
            have preserved := DataSem.popEnv_resourceLe clamped next pop
            simpa [DataSem.evaluate, sourceRun, found, distinct, cut, positive, bodyRun, DataSem.fixClock,
              arity, pop, clamped, DataSem.ResourceLe, DataSem.setVars, entry] using preserved
        · simp [DataSem.evaluate, sourceRun, found, distinct, cut, positive, bodyRun, DataSem.fixClock,
            arity, DataSem.ResourceLe, BackendProps.optionLe_refl, entry]

/-- A direct returning call with a handler propagates a callee allocation
failure and its resource bounds, even if the source subsequently runs the
handler. This is Lean-side simulation infrastructure. -/
theorem returningCall64_direct_handler_outOfSpace {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body handlerBody : DataLang.Prog)
    (handlerName : Nat) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0)
    (calleeFailure : outOfSpace64 conf callee 2 body
      (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
          (WordSemStateFiniteExact.decClock target)))) :
    outOfSpace64 conf secn label (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source target := by
  let sourceEntry := DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
      (WordSemStateFiniteExact.decClock target))
  obtain ⟨targetLast, bodyRun, bound, events, unsafeProof⟩ := calleeFailure
  let targetFinal := (WordSemStateFiniteExact.fixClock targetEntry
    ((some .notEnoughSpace : Option (WordSemResult 64)), targetLast)).2
  have targetFix : WordSemStateFiniteExact.fixClock targetEntry
      (WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry) =
        (some .notEnoughSpace, targetFinal) := by
    rw [bodyRun]
    rfl
  obtain ⟨wordCode, wordCut, notEmpty, mappedDistinct⟩ :=
    returningCall64_direct_setup conf secn label l1 l2 source target locs related callee names returns live saved values args body size
      sourceRun wordRun found cut distinct
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  have targetRun : WordSemStateFiniteExact.evaluate
      (compileControl64 conf secn label (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody)))).1 target =
        (some .notEnoughSpace, targetFinal) := by
    have compiled : (compileControl64 conf secn label (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody)))).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) (some callee) (names.map adjustVar)
          (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1)) := by
      conv_lhs => unfold compileControl64
      simp only [compileControl?]
      rw [compileControl64_checked conf secn (label + 2) handlerBody]
      rfl
    rw [compiled]
    simp only [adjustSets] at wordCut
    dsimp [targetEntry] at targetFix
    simp only [WordSemStateFiniteExact.evaluate, wordRun, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive]
    rw [targetFix]
    simp
  have sourceResource := returningCall64_handler_sourceResource source callee names returns live saved values body handlerBody handlerName size
    sourceRun found cut distinct positive
  have targetBound : BackendProps.optionLe targetFinal.stackMax (DataSem.evaluate body sourceEntry).2.stackMax := by
    simpa [targetFinal, WordSemStateFiniteExact.fixClock, sourceEntry, targetEntry] using bound
  have targetEvents : targetFinal.ffi.ioEvents <+: (DataSem.evaluate body sourceEntry).2.ffi.ioEvents := by
    simpa [targetFinal, WordSemStateFiniteExact.fixClock, sourceEntry, targetEntry] using events
  refine ⟨targetFinal, targetRun, ?_, ?_, ?_⟩
  · exact BackendProps.optionLe_trans _ _ _ ⟨targetBound, sourceResource.2.1⟩
  · exact List.IsPrefix.trans targetEvents sourceResource.1
  · intro active
    have beforeUnsafe : (DataSem.evaluate body sourceEntry).2.safeForSpace = false := unsafeProof active
    cases safeAfter : (DataSem.evaluate (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source).2.safeForSpace with
    | false => rfl
    | true =>
      have beforeSafe := sourceResource.2.2 safeAfter
      simp [sourceEntry, beforeUnsafe] at beforeSafe


/-- A caught exception inherits its handler's ordinary outcome or actual
allocation failure, with source and target clocks and handler state preserved. -/
theorem caughtCall64_direct_outcomesWithSpace {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
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
  rcases handlerCorrect handlerSource handlerTarget sourceCode sourceClock handlerRelated handlerSafe with ordinary | failure
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
theorem call64_direct_handler_outcomesWithSpace {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
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
    (calleeCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) → (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      outcomesWithSpace64 conf callee 2 secn label body s t ((l1, l2) :: locs))
    (calleeCode : (DataSem.evaluate body
      (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))).2.code = source.code)
    (handlerCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock →
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate handlerBody s).1 ≠ some (.err (.abort .typeError)) →
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
    rcases calleeCorrect (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))) _ rfl
        (by simp [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]; omega) entryRelated calleeSafe with ordinary | failure
    · rcases ordinary with continued | returned | timeout | raised
      · obtain ⟨sourceLast, targetLast, sr, tr, after⟩ := continued
        simp only [DataSem.evaluate, sourceRun, found, distinct, cut, zero, ↓reduceIte, Option.isSome_some] at safe
        rw [sr] at safe
        simp [DataSem.fixClock] at safe
      · exact Or.inl (Or.inl (returningCall64_direct_handler_of_safe conf secn label l1 l2 source target locs related
          callee names returns live saved values args body handlerBody handlerName size sourceRun wordRun found cut distinct zero safe returned))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (returningCall64_direct_handler_callee_timeout conf secn label l1 l2 source target locs related
          callee names returns live saved values args body handlerBody handlerName size sourceRun wordRun found cut distinct zero timeout))))
      · exact caughtCall64_direct_outcomesWithSpace conf secn label l1 l2 source target locs related callee names returns live saved
          values args body handlerBody handlerName size sourceRun wordRun found cut distinct zero safe raised calleeCode handlerCorrect
    · exact Or.inr (returningCall64_direct_handler_outOfSpace conf secn label l1 l2 source target locs related
        callee names returns live saved values args body handlerBody handlerName size sourceRun wordRun found cut distinct zero failure)

/-- Source safety supplies direct-call setup for a call with a handler;
the callee and handler induction hypotheses admit allocation failure. -/
theorem call64_direct_handler_withSpace_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (handlerName : Nat) (handlerBody : DataLang.Prog)
    (safe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (body : DataLang.Prog) (args : List DataSem.Value) (size : Option Nat),
      DataSem.findCode (some callee) args source.code source.stackFrameSizes = some (args, body, size) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) → (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
        outcomesWithSpace64 conf callee 2 secn label body s t ((l1, l2) :: locs))
    (calleePreserves : ∀ (body : DataLang.Prog) (args : List DataSem.Value) (size : Option Nat) (saved : Spt DataSem.Value),
      DataSem.findCode (some callee) args source.code source.stackFrameSizes = some (args, body, size) →
      DataSem.cutEnv live source.locals = some saved →
      (DataSem.evaluate body (DataSem.callEnv args size (DataSem.pushEnv saved true (DataSem.decClock source)))).2.code = source.code)
    (handlerCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock →
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate handlerBody s).1 ≠ some (.err (.abort .typeError)) →
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
          exact call64_direct_handler_outcomesWithSpace conf secn label l1 l2 source target locs related callee names returns live saved
            values words body handlerBody handlerName size sourceRun wordRun found cut distinct safe
            (calleeCorrect body values size found) (calleePreserves body values size saved found cut) handlerCorrect
      · simp [DataSem.evaluate, sourceRun, found, distinct] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
