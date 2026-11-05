import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.TailCallSpace
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.UnhandledCall
import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall

/-! Resource propagation through returning calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Returning to a direct caller cannot decrease the callee's recorded
resources. The statement also covers malformed returns and failed frame pops;
those executions become type errors but still retain the resource fields.
This is Flapjack infrastructure for allocation-failure propagation. -/
theorem returningCall64_sourceResource {C F : Type}
    (source : DataSem.State C F) (callee : Nat) (names returns : List Nat) (live : NumSet)
    (saved : Spt DataSem.Value) (values : List DataSem.Value) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0) :
    DataSem.ResourceLe
      (DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))).2
      (DataSem.evaluate (.call (some (returns, live)) (some callee) names none) source).2 := by
  let entry := DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))
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
        cases error <;>
          simp [DataSem.evaluate, sourceRun, found, distinct, cut, positive, bodyRun, DataSem.fixClock,
            DataSem.ResourceLe, BackendProps.optionLe_refl, entry]
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

/-- A direct returning call propagates an actual allocation failure from its
callee. The caller's final source resources bound the failed target state even
when the source callee subsequently returns and its frame is restored. -/
theorem returningCall64_direct_outOfSpace {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0)
    (calleeFailure : outOfSpace64 conf callee 2 body
      (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          none (WordSemStateFiniteExact.decClock target)))) :
    outOfSpace64 conf secn label (.call (some (returns, live)) (some callee) names none) source target := by
  let sourceEntry := DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      none (WordSemStateFiniteExact.decClock target))
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
      (compileControl64 conf secn label (.call (some (returns, live)) (some callee) names none)).1 target =
        (some .notEnoughSpace, targetFinal) := by
    have compiled : (compileControl64 conf secn label (.call (some (returns, live)) (some callee) names none)).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) (some callee) (names.map adjustVar) none := rfl
    rw [compiled]
    simp only [adjustSets] at wordCut
    dsimp [targetEntry] at targetFix
    simp only [WordSemStateFiniteExact.evaluate, wordRun, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive]
    rw [targetFix]
    simp
  have sourceResource := returningCall64_sourceResource source callee names returns live saved values body size
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
    cases safeAfter : (DataSem.evaluate (.call (some (returns, live)) (some callee) names none) source).2.safeForSpace with
    | false => rfl
    | true =>
      have beforeSafe := sourceResource.2.2 safeAfter
      simp [sourceEntry, beforeUnsafe] at beforeSafe

/-- A direct returning call without a handler inherits the ordinary or
allocation-failure outcome of its selected callee, including timeout. -/
theorem call64_direct_noHandler_outcomesWithSpace {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
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
      s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) →
      (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      outcomesWithSpace64 conf callee 2 secn label body s t ((l1, l2) :: locs)) :
    outcomesWithSpace64 conf secn label l1 l2 (.call (some (returns, live)) (some callee) names none) source target locs := by
  by_cases zero : source.clock = 0
  · exact Or.inl (Or.inr (Or.inr (Or.inl (returningCall64_direct_zero_timeout conf secn label l1 l2 source target locs related
      callee names returns live saved values args body size sourceRun wordRun found cut distinct zero))))
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
    rcases calleeCorrect (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))) _ rfl
        (by simp [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]; omega) entryRelated calleeSafe with ordinary | failure
    · rcases ordinary with continued | returned | timeout | raised
      · obtain ⟨sourceLast, targetLast, sr, tr, after⟩ := continued
        simp only [DataSem.evaluate, sourceRun, found, distinct, cut, zero, ↓reduceIte, Option.isSome_none] at safe
        rw [sr] at safe
        simp [DataSem.fixClock] at safe
      · exact Or.inl (Or.inl (returningCall64_direct_of_safe conf secn label l1 l2 source target locs related
          callee names returns live saved values args body size sourceRun wordRun found cut distinct zero safe returned))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (returningCall64_direct_callee_timeout conf secn label l1 l2 source target locs related
          callee names returns live saved values args body size sourceRun wordRun found cut distinct zero timeout))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (unhandledCall64_direct conf secn label l1 l2 source target locs related
          callee names returns live saved values args body size sourceRun wordRun found cut distinct zero raised))))
    · exact Or.inr (returningCall64_direct_outOfSpace conf secn label l1 l2 source target locs related
        callee names returns live saved values args body size sourceRun wordRun found cut distinct zero failure)

/-- Source safety supplies argument lookup, arity, distinct destinations, and
the live-set cut for a direct returning call. The sole recursive premise is
the smaller-clock callee simulation. -/
theorem call64_direct_noHandler_withSpace_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet)
    (safe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (body : DataLang.Prog) (args : List DataSem.Value) (size : Option Nat),
      DataSem.findCode (some callee) args source.code source.stackFrameSizes = some (args, body, size) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) →
        (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
        outcomesWithSpace64 conf callee 2 secn label body s t ((l1, l2) :: locs)) :
    outcomesWithSpace64 conf secn label l1 l2 (.call (some (returns, live)) (some callee) names none) source target locs := by
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
          exact call64_direct_noHandler_outcomesWithSpace conf secn label l1 l2 source target locs related callee names returns live saved
            values words body size sourceRun wordRun found cut distinct safe (calleeCorrect body values size found)
      · simp [DataSem.evaluate, sourceRun, found, distinct] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
