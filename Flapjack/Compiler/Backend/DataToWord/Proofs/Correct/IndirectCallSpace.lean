import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.HandlerCallSpace
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectTailCall

/-! Allocation-failure propagation through indirect calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A resolved source-safe indirect tail call propagates the callee's actual
allocation failure and its resource and event bounds. This is Flapjack
simulation infrastructure rather than a separate HOL theorem port. -/
theorem tailCall64_indirect_outOfSpace {C F : Type} (conf : Config) (secn fresh : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (names : List Nat) (name label : Nat) (values : List DataSem.Value) (words : List (WordLocW 64))
    (l1 l2 : Nat) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars (names ++ [name]) source.locals = some (values ++ [.codePtr label]))
    (wordRun : WordSemStateFiniteExact.getVars (0 :: (names ++ [name]).map adjustVar) target =
      some ((.loc l1 l2 :: words) ++ [.loc label 0]))
    (sourceCode : DataSem.findCode none (values ++ [.codePtr label]) source.code source.stackFrameSizes = some (values, body, size))
    (wordCode : wordSemFindCode none ((.loc l1 l2 :: words) ++ [.loc label 0]) target.code target.stackSize =
      some (.loc l1 l2 :: words, (compileControl64 conf label 2 body).1, size))
    (positive : source.clock ≠ 0) (clock : target.clock = source.clock)
    (safe : (DataSem.evaluate (.call none none (names ++ [name]) none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeFailure : outOfSpace64 conf label 2 body
      (DataSem.callEnv values size (DataSem.decClock source))
      (WordSemStateFiniteExact.callEnv (.loc l1 l2 :: words) size (WordSemStateFiniteExact.decClock target))) :
    outOfSpace64 conf secn fresh (.call none none (names ++ [name]) none) source target := by
  obtain ⟨targetFinal, targetRun, bound, events, unsafeProof⟩ := calleeFailure
  cases sourceBody : DataSem.evaluate body (DataSem.callEnv values size (DataSem.decClock source)) with
  | mk sourceResult sourceFinal =>
    cases sourceResult with
    | none => simp [DataSem.evaluate, sourceRun, sourceCode, positive, sourceBody] at safe
    | some sourceResult =>
      have evaluations := tailCall64_indirect_evaluations conf secn fresh source target names name label values words l1 l2 body size
        sourceRun wordRun sourceCode wordCode positive clock (some sourceResult) sourceFinal
        (some .notEnoughSpace) targetFinal sourceBody targetRun (by simp) rfl
      refine ⟨targetFinal, evaluations.2, ?_, ?_, ?_⟩
      · simpa [evaluations.1, sourceBody] using bound
      · simpa [evaluations.1, sourceBody] using events
      · simpa [evaluations.1, sourceBody] using unsafeProof

/-- A resolved indirect tail call inherits ordinary outcomes and allocation
failure from its smaller-clock callee, including the zero-clock case. -/
theorem tailCall64_indirect_outcomesWithSpace {C F : Type} (conf : Config) (secn fresh l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (label : Nat) (names : List Nat) (name : Nat) (values : List DataSem.Value) (body : DataLang.Prog)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (pointer : DataSem.getVar name source.locals = some (.codePtr label))
    (lookup : sptLookup label source.code = some (values.length, body))
    (safe : (DataSem.evaluate (.call none none (names ++ [name]) none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock → stateRel64 conf l1 l2 s t none locs →
      (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      outcomesWithSpace64 conf label 2 l1 l2 body s t locs) :
    outcomesWithSpace64 conf secn fresh l1 l2 (.call none none (names ++ [name]) none) source target locs := by
  obtain ⟨words, sourceAll, wordAll, sourceCode, wordCode, calleeRelated⟩ :=
    stateRel64_findCode_indirect_callEnv conf l1 l2 source target locs related label names name values body sourceRun pointer lookup
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by simpa [related.2.1] using zero
    apply Or.inl; apply Or.inr; apply Or.inr; apply Or.inl
    refine ⟨DataSem.flushState true source, WordSemStateFiniteExact.flushState true target, ?_, ?_, related.1, ?_⟩
    · simp [DataSem.evaluate, sourceAll, sourceCode, zero]
    · have compiled : (compileControl64 conf secn fresh (.call none none (names ++ [name]) none)).1 =
          .call none none (0 :: (names ++ [name]).map adjustVar) none := rfl
      rw [compiled]
      simp only [List.map_append, List.map_cons, List.map_nil] at wordAll
      simp only [List.cons_append] at wordCode
      simp [WordSemStateFiniteExact.evaluate, wordAll, wordSemBadDestArgs, wordSemAddRetLoc, wordCode, targetZero]
    · exact related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · have calleeSafe : (DataSem.evaluate body (DataSem.callEnv values (sptLookup label source.stackFrameSizes)
        (DataSem.decClock source))).1 ≠ some (.err (.abort .typeError)) := by
      intro bad
      cases run : DataSem.evaluate body (DataSem.callEnv values (sptLookup label source.stackFrameSizes) (DataSem.decClock source)) with
      | mk result state =>
        have eq : result = some (.err (.abort .typeError)) := by simpa [run] using bad
        subst result
        simp [DataSem.evaluate, sourceAll, sourceCode, zero, run] at safe
    rcases calleeCorrect (DataSem.callEnv values (sptLookup label source.stackFrameSizes) (DataSem.decClock source)) _ rfl
        (by simp [DataSem.callEnv, DataSem.decClock]; omega) calleeRelated calleeSafe with ordinary | failure
    · rcases ordinary with continued | returned | timeout | raised
      · obtain ⟨sourceNext, targetNext, sr, tr, after⟩ := continued
        simp [DataSem.evaluate, sourceAll, sourceCode, zero, sr] at safe
      · obtain ⟨result, targetValues, sourceNext, targetNext, lengths, sr, tr, after⟩ := returned
        have eqs := tailCall64_indirect_evaluations conf secn fresh source target names name label values words l1 l2 body _
          sourceAll wordAll sourceCode wordCode zero related.2.1 _ sourceNext _ targetNext sr tr (by simp) rfl
        exact Or.inl (Or.inr (Or.inl ⟨result, targetValues, sourceNext, targetNext, lengths, eqs.1, eqs.2, after⟩))
      · obtain ⟨sourceNext, targetNext, sr, tr, ffi, bound⟩ := timeout
        have eqs := tailCall64_indirect_evaluations conf secn fresh source target names name label values words l1 l2 body _
          sourceAll wordAll sourceCode wordCode zero related.2.1 _ sourceNext _ targetNext sr tr (by simp) rfl
        exact Or.inl (Or.inr (Or.inr (Or.inl ⟨sourceNext, targetNext, eqs.1, eqs.2, ffi, bound⟩)))
      · obtain ⟨result, targetValue, sourceNext, targetNext, a, b, r1, r2, remaining, sr, tr, ⟨jumpState, jump⟩, ffi, bound, locations, after⟩ := raised
        have eqs := tailCall64_indirect_evaluations conf secn fresh source target names name label values words l1 l2 body _
          sourceAll wordAll sourceCode wordCode zero related.2.1 _ sourceNext _ targetNext sr tr (by simp) rfl
        exact Or.inl (Or.inr (Or.inr (Or.inr ⟨result, targetValue, sourceNext, targetNext, a, b, r1, r2, remaining,
          eqs.1, eqs.2, callEnv_jumpExc_destination target jumpState _ _ a b jump, ffi, bound, locations, after⟩)))
    · exact Or.inr (tailCall64_indirect_outOfSpace conf secn fresh source target names name label values words l1 l2 body _
        sourceAll wordAll sourceCode wordCode zero related.2.1 safe failure)

/-- Every source-safe indirect tail call is simulated when the selected
callee satisfies the smaller-clock allocation-aware induction hypothesis. -/
theorem tailCall64_indirect_withSpace_of_safe {C F : Type} (conf : Config) (secn fresh l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names : List Nat)
    (safe : (DataSem.evaluate (.call none none names none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeCorrect : ∀ (label arity : Nat) (body : DataLang.Prog),
      sptLookup label source.code = some (arity, body) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        s.code = source.code → s.clock < source.clock → stateRel64 conf l1 l2 s t none locs →
        (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
        outcomesWithSpace64 conf label 2 l1 l2 body s t locs) :
    outcomesWithSpace64 conf secn fresh l1 l2 (.call none none names none) source target locs := by
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
      | codePtr label =>
        cases lookup : sptLookup label source.code with
        | none => simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc, lookup] at safe
        | some entry =>
          obtain ⟨arity, body⟩ := entry
          by_cases length : values.length = arity
          · subst arity
            exact tailCall64_indirect_outcomesWithSpace conf secn fresh l1 l2 source target locs related label names name values body
              prefixRun finalRun lookup safe (calleeCorrect label values.length body lookup)
          · simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc, lookup, length] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
