import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorReturningCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectReturningCallSpace

/-! Source-space-safe indirect calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- An indirect tail call transfers source space safety to its callee. -/
theorem tailCall64_indirect_outcomesWithSpace_safe {C F : Type} (conf : Config) (secn fresh l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (label : Nat) (names : List Nat) (name : Nat) (values : List DataSem.Value) (body : DataLang.Prog)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (pointer : DataSem.getVar name source.locals = some (.codePtr label))
    (lookup : sptLookup label source.code = some (values.length, body))
    (safe : (DataSem.evaluate (.call none none (names ++ [name]) none) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call none none (names ++ [name]) none) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock → stateRel64 conf l1 l2 s t none locs →
      (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body s).2.safeForSpace = true →
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
    have calleeSpace : (DataSem.evaluate body (DataSem.callEnv values (sptLookup label source.stackFrameSizes)
        (DataSem.decClock source))).2.safeForSpace = true := by
      cases run : DataSem.evaluate body (DataSem.callEnv values (sptLookup label source.stackFrameSizes) (DataSem.decClock source)) with
      | mk result state =>
        cases result with
        | none => simp [DataSem.evaluate, sourceAll, sourceCode, zero, run] at safe
        | some result => simpa [DataSem.evaluate, sourceAll, sourceCode, zero, run] using spaceSafe
    rcases calleeCorrect (DataSem.callEnv values (sptLookup label source.stackFrameSizes) (DataSem.decClock source)) _ rfl
        (by simp [DataSem.callEnv, DataSem.decClock]; omega) calleeRelated calleeSafe calleeSpace with ordinary | failure
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
theorem tailCall64_indirect_withSpace_and_spaceSafe {C F : Type} (conf : Config) (secn fresh l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names : List Nat)
    (safe : (DataSem.evaluate (.call none none names none) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call none none names none) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (label arity : Nat) (body : DataLang.Prog),
      sptLookup label source.code = some (arity, body) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        s.code = source.code → s.clock < source.clock → stateRel64 conf l1 l2 s t none locs →
        (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body s).2.safeForSpace = true →
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
            exact tailCall64_indirect_outcomesWithSpace_safe conf secn fresh l1 l2 source target locs related label names name values body
              prefixRun finalRun lookup safe spaceSafe (calleeCorrect label values.length body lookup)
          · simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc, lookup, length] at safe

/-- An indirect returning call transfers source space safety to its callee. -/
theorem call64_indirect_noHandler_outcomesWithSpace_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
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
    (spaceSafe : (DataSem.evaluate (.call (some (returns, live)) none (names ++ [lastName]) none) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) → (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body s).2.safeForSpace = true →
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
    have calleeSpace := (returningCall64_indirect_sourceResource source callee names returns lastName live saved values body size
      sourceAll sourceCode' cut distinct zero).2.2 spaceSafe
    rcases calleeCorrect (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))) _ rfl
        (by simp [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]; omega) entryRelated' calleeSafe calleeSpace with ordinary | failure
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
theorem call64_indirect_noHandler_withSpace_and_spaceSafe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names returns : List Nat) (live : NumSet)
    (safe : (DataSem.evaluate (.call (some (returns, live)) none names none) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call (some (returns, live)) none names none) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (callee arity : Nat) (body : DataLang.Prog),
      sptLookup callee source.code = some (arity, body) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) →
        (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body s).2.safeForSpace = true →
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
                exact call64_indirect_noHandler_outcomesWithSpace_safe conf secn label l1 l2 source target locs related callee names returns name live saved
                  values words body _ prefixRun wordRun finalRun lookup rfl cut distinct safe spaceSafe (calleeCorrect callee values.length body lookup)
            · simp [DataSem.evaluate, run, found, distinct] at safe
          · simp [DataSem.evaluate, run, DataSem.findCode, holLast_snoc, lookup, length] at safe

/-- Constructor-aware fragments with direct and indirect calls. -/
inductive IndirectConstructorFragment : DataLang.Prog → Prop where
  | base {program : DataLang.Prog} : VerifiedWithConstructors program → IndirectConstructorFragment program
  | seq {first second : DataLang.Prog} : IndirectConstructorFragment first → IndirectConstructorFragment second →
      IndirectConstructorFragment (.seq first second)
  | ite (name : Nat) {yes no : DataLang.Prog} : IndirectConstructorFragment yes → IndirectConstructorFragment no →
      IndirectConstructorFragment (.ifThenElse name yes no)
  | tailCall (callee : Nat) (names : List Nat) : IndirectConstructorFragment (.call none (some callee) names none)
  | returningCall (callee : Nat) (names returns : List Nat) (live : NumSet) :
      IndirectConstructorFragment (.call (some (returns, live)) (some callee) names none)
  | indirectTailCall (names : List Nat) : IndirectConstructorFragment (.call none none names none)
  | indirectReturningCall (names returns : List Nat) (live : NumSet) :
      IndirectConstructorFragment (.call (some (returns, live)) none names none)

/-- Each callable body belongs to the indirect-call constructor fragment. -/
def IndirectConstructorFragmentCode (code : Spt (Nat × DataLang.Prog)) : Prop :=
  ∀ label arity body, sptLookup label code = some (arity, body) → IndirectConstructorFragment body

/-- The fragment preserves source code across recursive calls. -/
theorem indirectConstructorFragment_code {C F : Type} (program : DataLang.Prog)
    (fragment : IndirectConstructorFragment program) (state : DataSem.State C F)
    (closed : IndirectConstructorFragmentCode state.code) : (DataSem.evaluate program state).2.code = state.code := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), IndirectConstructorFragment program →
      ∀ state : DataSem.State C F, state.clock = clock → IndirectConstructorFragmentCode state.code →
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
        have midClosed : IndirectConstructorFragmentCode mid.code := by simpa [codeEq] using closed
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
          have nextClosed : IndirectConstructorFragmentCode next.code := by simpa [codeEq] using closed
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
          have nextClosed : IndirectConstructorFragmentCode next.code := by simpa [codeEq] using closed
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
          have nextClosed : IndirectConstructorFragmentCode next.code := by simpa [codeEq] using closed
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
          have nextClosed : IndirectConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq
          cases handlerEq
  exact allClocks state.clock program fragment state rfl closed

/-- Closed constructor-aware programs, including mutually recursive direct and
indirect calls, have an ordinary related outcome or permitted allocation failure.
This is a conditional Flapjack simulation, not unrestricted HOL correctness. -/
theorem indirectConstructorFragment64 {C F : Type} (conf : Config) (program : DataLang.Prog)
    (fragment : IndirectConstructorFragment program) :
    ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
      (locs : List (Nat × Nat)), IndirectConstructorFragmentCode source.code →
      stateRel64 conf l1 l2 source target none locs →
      (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate program source).2.safeForSpace = true →
      outcomesWithSpace64 conf secn label l1 l2 program source target locs := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), IndirectConstructorFragment program →
      ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
        (locs : List (Nat × Nat)), source.clock = clock → IndirectConstructorFragmentCode source.code →
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
        have firstCode := indirectConstructorFragment_code first firstFrag source closed
        apply seq64_outcomesWithSpace_safe_closed conf secn label l1 l2 first second source target locs related safe spaceSafe
          firstOutcome firstCode
        intro s t codeEq bound rel valid space
        have nextClosed : IndirectConstructorFragmentCode s.code := by simpa [codeEq] using closed
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
              have nextClosed : IndirectConstructorFragmentCode (DataSem.callEnv values size (DataSem.decClock source)).code := by
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
        have nextClosed : IndirectConstructorFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs)
          rfl nextClosed rel valid space
      | indirectTailCall names =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
        apply tailCall64_indirect_withSpace_and_spaceSafe conf secn label l1 l2 source target locs related names safe spaceSafe
        intro callee arity body lookup s t codeEq smaller rel valid space
        have member := closed callee arity body lookup
        have nextClosed : IndirectConstructorFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 l1 l2 s t locs rfl nextClosed rel valid space
      | indirectReturningCall names returns live =>
        intro secn label l1 l2 source target locs eq closed related safe spaceSafe
        apply call64_indirect_noHandler_withSpace_and_spaceSafe conf secn label l1 l2 source target locs related
          names returns live safe spaceSafe
        intro callee arity body lookup s t codeEq smaller rel valid space
        have member := closed callee arity body lookup
        have nextClosed : IndirectConstructorFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs)
          rfl nextClosed rel valid space
  intro secn label l1 l2 source target locs closed related safe spaceSafe
  exact allClocks source.clock program fragment secn label l1 l2 source target locs rfl closed related safe spaceSafe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
