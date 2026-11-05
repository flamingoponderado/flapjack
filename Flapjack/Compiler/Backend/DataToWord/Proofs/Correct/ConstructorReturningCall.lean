import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorTailCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ReturningCallSpace

/-! Source-space-safe returning calls for constructor-aware fragments. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Direct returning-call outcomes, preserving source space safety for the callee. -/
theorem call64_direct_noHandler_outcomesWithSpace_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup)
    (safe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names none) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names none) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) →
      (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body s).2.safeForSpace = true →
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
    have calleeSpace := (returningCall64_sourceResource source callee names returns live saved values body size
      sourceRun found cut distinct zero).2.2 spaceSafe
    rcases calleeCorrect (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))) _ rfl
        (by simp [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]; omega) entryRelated calleeSafe calleeSpace with ordinary | failure
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
theorem call64_direct_noHandler_withSpace_and_spaceSafe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet)
    (safe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names none) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call (some (returns, live)) (some callee) names none) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (body : DataLang.Prog) (args : List DataSem.Value) (size : Option Nat),
      DataSem.findCode (some callee) args source.code source.stackFrameSizes = some (args, body, size) →
      ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
        s.code = source.code → s.clock < source.clock → stateRel64 conf secn label s t none ((l1, l2) :: locs) →
        (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body s).2.safeForSpace = true →
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
          exact call64_direct_noHandler_outcomesWithSpace_safe conf secn label l1 l2 source target locs related callee names returns live saved
            values words body size sourceRun wordRun found cut distinct safe spaceSafe (calleeCorrect body values size found)
      · simp [DataSem.evaluate, sourceRun, found, distinct] at safe

/-- Constructor-aware fragments with direct tail and returning calls. -/
inductive ReturningConstructorFragment : DataLang.Prog → Prop where
  | base {program : DataLang.Prog} : VerifiedWithConstructors program → ReturningConstructorFragment program
  | seq {first second : DataLang.Prog} : ReturningConstructorFragment first → ReturningConstructorFragment second →
      ReturningConstructorFragment (.seq first second)
  | ite (name : Nat) {yes no : DataLang.Prog} : ReturningConstructorFragment yes → ReturningConstructorFragment no →
      ReturningConstructorFragment (.ifThenElse name yes no)
  | tailCall (callee : Nat) (names : List Nat) : ReturningConstructorFragment (.call none (some callee) names none)
  | returningCall (callee : Nat) (names returns : List Nat) (live : NumSet) :
      ReturningConstructorFragment (.call (some (returns, live)) (some callee) names none)

/-- Each callable body belongs to the direct-call constructor fragment. -/
def ReturningConstructorFragmentCode (code : Spt (Nat × DataLang.Prog)) : Prop :=
  ∀ label arity body, sptLookup label code = some (arity, body) → ReturningConstructorFragment body

/-- The fragment preserves source code across recursive direct calls. -/
theorem returningConstructorFragment_code {C F : Type} (program : DataLang.Prog)
    (fragment : ReturningConstructorFragment program) (state : DataSem.State C F)
    (closed : ReturningConstructorFragmentCode state.code) : (DataSem.evaluate program state).2.code = state.code := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), ReturningConstructorFragment program →
      ∀ state : DataSem.State C F, state.clock = clock → ReturningConstructorFragmentCode state.code →
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
        have midClosed : ReturningConstructorFragmentCode mid.code := by simpa [codeEq] using closed
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
          have nextClosed : ReturningConstructorFragmentCode next.code := by simpa [codeEq] using closed
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
          have nextClosed : ReturningConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq
          cases handlerEq
  exact allClocks state.clock program fragment state rfl closed

/-- Closed constructor-aware direct-call programs, including mutually recursive
tail and returning calls, have an ordinary related outcome or permitted allocation failure.
This is a conditional Flapjack simulation, not unrestricted HOL correctness. -/
theorem returningConstructorFragment64 {C F : Type} (conf : Config) (program : DataLang.Prog)
    (fragment : ReturningConstructorFragment program) :
    ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
      (locs : List (Nat × Nat)), ReturningConstructorFragmentCode source.code →
      stateRel64 conf l1 l2 source target none locs →
      (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate program source).2.safeForSpace = true →
      outcomesWithSpace64 conf secn label l1 l2 program source target locs := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), ReturningConstructorFragment program →
      ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
        (locs : List (Nat × Nat)), source.clock = clock → ReturningConstructorFragmentCode source.code →
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
        have firstCode := returningConstructorFragment_code first firstFrag source closed
        apply seq64_outcomesWithSpace_safe_closed conf secn label l1 l2 first second source target locs related safe spaceSafe
          firstOutcome firstCode
        intro s t codeEq bound rel valid space
        have nextClosed : ReturningConstructorFragmentCode s.code := by simpa [codeEq] using closed
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
              have nextClosed : ReturningConstructorFragmentCode (DataSem.callEnv values size (DataSem.decClock source)).code := by
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
        have nextClosed : ReturningConstructorFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs)
          rfl nextClosed rel valid space
  intro secn label l1 l2 source target locs closed related safe spaceSafe
  exact allClocks source.clock program fragment secn label l1 l2 source target locs rfl closed related safe spaceSafe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
