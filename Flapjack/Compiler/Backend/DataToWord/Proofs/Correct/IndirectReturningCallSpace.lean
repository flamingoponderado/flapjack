import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectCallSpace
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectUnhandledCall

/-! Allocation failure propagation through indirect returning calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- An indirect caller preserves the callee's resource observations, including
when returning or restoring the caller frame fails. This is Flapjack-specific
simulation infrastructure. -/
theorem returningCall64_indirect_sourceResource {C F : Type}
    (source : DataSem.State C F) (callee : Nat) (names returns : List Nat) (lastName : Nat) (live : NumSet)
    (saved : Spt DataSem.Value) (values : List DataSem.Value) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars (names ++ [lastName]) source.locals = some (values ++ [.codePtr callee]))
    (found : DataSem.findCode none (values ++ [.codePtr callee]) source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0) :
    DataSem.ResourceLe
      (DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))).2
      (DataSem.evaluate (.call (some (returns, live)) none (names ++ [lastName]) none) source).2 := by
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

/-- An indirect caller propagates an actual allocation failure from the
selected callee, preserving resource and event bounds. -/
theorem returningCall64_indirect_outOfSpace {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
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
    (calleeFailure : outOfSpace64 conf callee 2 body
      (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          none (WordSemStateFiniteExact.decClock target)))) :
    outOfSpace64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) none) source target := by
  subst size
  let sourceEntry := DataSem.callEnv values (sptLookup callee source.stackFrameSizes) (DataSem.pushEnv saved false (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) (sptLookup callee source.stackFrameSizes)
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
  obtain ⟨sourceAll, wordAll, sourceCode, wordCode, wordCut, notEmpty, mappedDistinct, _⟩ :=
    indirectCall64_setup conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body
      sourceRun wordRun pointer lookup cut distinct none
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  have targetRun : WordSemStateFiniteExact.evaluate
      (compileControl64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) none)).1 target =
        (some .notEnoughSpace, targetFinal) := by
    have compiled : (compileControl64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) none)).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) none ((names ++ [lastName]).map adjustVar) none := rfl
    rw [compiled]
    simp only [adjustSets] at wordCut
    simp only [List.map_append, List.map_cons, List.map_nil] at wordAll
    simp only [List.cons_append] at wordCode
    dsimp [targetEntry] at targetFix
    simp only [WordSemStateFiniteExact.evaluate, wordAll, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive, List.map_append, List.map_cons, List.map_nil]
    rw [targetFix]
    simp
  have sourceResource := returningCall64_indirect_sourceResource source callee names returns lastName live saved values body _
    sourceAll sourceCode cut distinct positive
  have targetBound : BackendProps.optionLe targetFinal.stackMax (DataSem.evaluate body sourceEntry).2.stackMax := by
    simpa [targetFinal, WordSemStateFiniteExact.fixClock, sourceEntry, targetEntry] using bound
  have targetEvents : targetFinal.ffi.ioEvents <+: (DataSem.evaluate body sourceEntry).2.ffi.ioEvents := by
    simpa [targetFinal, WordSemStateFiniteExact.fixClock, sourceEntry, targetEntry] using events
  refine ⟨targetFinal, targetRun, ?_, ?_, ?_⟩
  · exact BackendProps.optionLe_trans _ _ _ ⟨targetBound, sourceResource.2.1⟩
  · exact List.IsPrefix.trans targetEvents sourceResource.1
  · intro active
    have beforeUnsafe : (DataSem.evaluate body sourceEntry).2.safeForSpace = false := unsafeProof active
    cases safeAfter : (DataSem.evaluate (.call (some (returns, live)) none (names ++ [lastName]) none) source).2.safeForSpace with
    | false => rfl
    | true =>
      have beforeSafe := sourceResource.2.2 safeAfter
      simp [sourceEntry, beforeUnsafe] at beforeSafe

/-- A source-safe indirect call without a handler propagates ordinary outcomes
and actual allocation failure from its selected callee. -/
theorem call64_indirect_noHandler_outcomesWithSpace {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
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
      outcomesWithSpace64 conf callee 2 secn label body s t ((l1, l2) :: locs)) :
    outcomesWithSpace64 conf secn label l1 l2 (.call (some (returns, live)) none (names ++ [lastName]) none) source target locs := by
  obtain ⟨sourceAll, _, sourceCode, _, _, _, _, entryRelated⟩ :=
    indirectCall64_setup conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body
      sourceRun wordRun pointer lookup cut distinct none
  have sourceCode' : DataSem.findCode none (values ++ [.codePtr callee]) source.code source.stackFrameSizes = some (values, body, size) := by
    simpa [sizeEq] using sourceCode
  by_cases zero : source.clock = 0
  · exact Or.inl (Or.inr (Or.inr (Or.inl (returningCall64_indirect_zero_timeout conf secn label l1 l2 source target locs related
      callee names returns lastName live saved values args body size sourceRun wordRun pointer lookup sizeEq cut distinct zero))))
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
    rcases calleeCorrect (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))) _ rfl
        (by simp [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]; omega) entryRelated' calleeSafe with ordinary | failure
    · rcases ordinary with continued | returned | timeout | raised
      · obtain ⟨sourceLast, targetLast, sr, tr, after⟩ := continued
        simp only [DataSem.evaluate, sourceAll, sourceCode', distinct, cut, zero, ↓reduceIte, Option.isSome_none] at safe
        rw [sr] at safe
        simp [DataSem.fixClock] at safe
      · exact Or.inl (Or.inl (returningCall64_indirect_of_safe conf secn label l1 l2 source target locs related
          callee names returns lastName live saved values args body size sourceRun wordRun pointer lookup sizeEq cut distinct zero safe returned))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (returningCall64_indirect_callee_timeout conf secn label l1 l2 source target locs related
          callee names returns lastName live saved values args body size sourceRun wordRun pointer lookup sizeEq cut distinct zero timeout))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (unhandledCall64_indirect conf secn label l1 l2 source target locs related
          callee names returns lastName live saved values args body size sourceRun wordRun pointer lookup sizeEq cut distinct zero raised))))
    · exact Or.inr (returningCall64_indirect_outOfSpace conf secn label l1 l2 source target locs related
        callee names returns lastName live saved values args body size sourceRun wordRun pointer lookup sizeEq cut distinct zero failure)

/-- A safe indirect call is simulated when its selected body satisfies the
recursive simulation hypothesis. -/
theorem call64_indirect_noHandler_withSpace_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names returns : List Nat) (live : NumSet)
    (safe : (DataSem.evaluate (.call (some (returns, live)) none names none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (callee arity : Nat) (body : DataLang.Prog),
      sptLookup callee source.code = some (arity, body) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) →
        (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
        outcomesWithSpace64 conf callee 2 secn label body s t ((l1, l2) :: locs)) :
    outcomesWithSpace64 conf secn label l1 l2 (.call (some (returns, live)) none names none) source target locs := by
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
                exact call64_indirect_noHandler_outcomesWithSpace conf secn label l1 l2 source target locs related callee names returns name live saved
                  values words body _ prefixRun wordRun finalRun lookup rfl cut distinct safe (calleeCorrect callee values.length body lookup)
            · simp [DataSem.evaluate, run, found, distinct] at safe
          · simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc, lookup, length] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
