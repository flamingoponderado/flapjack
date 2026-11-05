import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorFragment
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.TailCallSpace
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CallFragment

/-! Direct tail calls to constructor-aware data fragments. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A positive-clock direct tail call inherits the outcome of its actual
callee when the source call is space-safe. -/
theorem tailCall64_direct_withSpace_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names : List Nat) (values : List DataSem.Value) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (positive : source.clock ≠ 0)
    (safe : (DataSem.evaluate (.call none (some callee) names none) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call none (some callee) names none) source).2.safeForSpace = true)
    (calleeCorrect : ∀ (t : WordSemStateFiniteExact 64 C F),
      stateRel64 conf l1 l2 (DataSem.callEnv values size (DataSem.decClock source)) t none locs →
      (DataSem.evaluate body (DataSem.callEnv values size (DataSem.decClock source))).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate body (DataSem.callEnv values size (DataSem.decClock source))).2.safeForSpace = true →
      outcomesWithSpace64 conf callee 2 l1 l2 body (DataSem.callEnv values size (DataSem.decClock source)) t locs) :
    outcomesWithSpace64 conf secn label l1 l2 (.call none (some callee) names none) source target locs := by
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
  have calleeSpace : (DataSem.evaluate body (DataSem.callEnv values size (DataSem.decClock source))).2.safeForSpace = true := by
    cases run : DataSem.evaluate body (DataSem.callEnv values size (DataSem.decClock source)) with
    | mk result state =>
      cases result with
      | none => simp [DataSem.evaluate, sourceRun, found, positive, run] at safe
      | some result => simpa [DataSem.evaluate, sourceRun, found, positive, run] using spaceSafe
  have calleeOutcome := calleeCorrect
    (WordSemStateFiniteExact.callEnv (.loc l1 l2 :: words) size (WordSemStateFiniteExact.decClock target))
    calleeRelated calleeSafe calleeSpace
  rcases calleeOutcome with ordinary | failure
  · rcases ordinary with continued | returned | timeout | raised
    · obtain ⟨sourceNext, targetNext, sr, tr, after⟩ := continued
      simp [DataSem.evaluate, sourceRun, found, positive, sr] at safe
    · obtain ⟨result, targetValues, sourceNext, targetNext, lengths, sr, tr, after⟩ := returned
      have eqs := tailCall64_direct_evaluations conf secn label l1 l2 source target locs related callee names values body size
        sourceRun found positive words wordRun _ sourceNext _ targetNext sr tr (by simp) rfl
      exact Or.inl (Or.inr (Or.inl ⟨result, targetValues, sourceNext, targetNext, lengths, eqs.1, eqs.2, after⟩))
    · obtain ⟨sourceNext, targetNext, sr, tr, ffi, bound⟩ := timeout
      have eqs := tailCall64_direct_evaluations conf secn label l1 l2 source target locs related callee names values body size
        sourceRun found positive words wordRun _ sourceNext _ targetNext sr tr (by simp) rfl
      exact Or.inl (Or.inr (Or.inr (Or.inl ⟨sourceNext, targetNext, eqs.1, eqs.2, ffi, bound⟩)))
    · obtain ⟨result, targetValue, sourceNext, targetNext, a, b, r1, r2, remaining, sr, tr, ⟨jumpState, jump⟩, ffi, bound, locations, after⟩ := raised
      have eqs := tailCall64_direct_evaluations conf secn label l1 l2 source target locs related callee names values body size
        sourceRun found positive words wordRun _ sourceNext _ targetNext sr tr (by simp) rfl
      exact Or.inl (Or.inr (Or.inr (Or.inr ⟨result, targetValue, sourceNext, targetNext, a, b, r1, r2, remaining,
        eqs.1, eqs.2, callEnv_jumpExc_destination target jumpState _ _ a b jump, ffi, bound, locations, after⟩)))
  · exact Or.inr (tailCall64_direct_outOfSpace conf secn label l1 l2 source target locs related callee names values body size
      sourceRun found positive safe words wordRun failure)

/-- A source-safe direct tail call is simulated when the resolved function
body belongs to the constructor-aware fragment, including clock exhaustion. -/
theorem tailCall64_direct_constructors_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names : List Nat)
    (closed : ∀ arity body, sptLookup callee source.code = some (arity, body) → VerifiedWithConstructors body)
    (safe : (DataSem.evaluate (.call none (some callee) names none) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.call none (some callee) names none) source).2.safeForSpace = true) :
    outcomesWithSpace64 conf secn label l1 l2 (.call none (some callee) names none) source target locs := by
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
        apply tailCall64_direct_withSpace_safe conf secn label l1 l2 source target locs related callee names values body size
          sourceRun found zero safe spaceSafe
        intro t rel valid space
        exact verifiedWithConstructors64 conf callee l1 l2 body (closed arity body lookup) 2
          (DataSem.callEnv values size (DataSem.decClock source)) t locs rel valid space

/-- Constructor-aware fragments preserve the source code table. -/
theorem verifiedWithConstructors_code {C F : Type} (program : DataLang.Prog)
    (fragment : VerifiedWithConstructors program) :
    ∀ state : DataSem.State C F, (DataSem.evaluate program state).2.code = state.code := by
  induction fragment with
  | established established => exact verifiedWithSpace_code _ established
  | constructor dest tag args nonempty =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.cons tag) args none state (doAppAux_cons_code tag)
  | @seq first second _ _ firstIH secondIH =>
    intro state
    exact DataSem.evaluate_seq_code_step first second state (firstIH state) (fun mid _ _ => secondIH mid)
  | @ite name yes no _ _ yesIH noIH =>
    intro state
    exact DataSem.evaluate_if_code_step name yes no state (yesIH state) (noIH state)

/-- Constructor-aware fragments with direct tail calls. -/
inductive TailConstructorFragment : DataLang.Prog → Prop where
  | base {program : DataLang.Prog} : VerifiedWithConstructors program → TailConstructorFragment program
  | seq {first second : DataLang.Prog} : TailConstructorFragment first → TailConstructorFragment second →
      TailConstructorFragment (.seq first second)
  | ite (name : Nat) {yes no : DataLang.Prog} : TailConstructorFragment yes → TailConstructorFragment no →
      TailConstructorFragment (.ifThenElse name yes no)
  | tailCall (callee : Nat) (names : List Nat) : TailConstructorFragment (.call none (some callee) names none)

/-- Each callable body belongs to the tail-call constructor fragment. -/
def TailConstructorFragmentCode (code : Spt (Nat × DataLang.Prog)) : Prop :=
  ∀ label arity body, sptLookup label code = some (arity, body) → TailConstructorFragment body

/-- The fragment preserves source code even across recursive tail calls. -/
theorem tailConstructorFragment_code {C F : Type} (program : DataLang.Prog)
    (fragment : TailConstructorFragment program) (state : DataSem.State C F)
    (closed : TailConstructorFragmentCode state.code) : (DataSem.evaluate program state).2.code = state.code := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), TailConstructorFragment program →
      ∀ state : DataSem.State C F, state.clock = clock → TailConstructorFragmentCode state.code →
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
        have midClosed : TailConstructorFragmentCode mid.code := by simpa [codeEq] using closed
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
          have nextClosed : TailConstructorFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq
          cases handlerEq
  exact allClocks state.clock program fragment state rfl closed

/-- Sequential composition with preserved code, clock and source space safety. -/
theorem seq64_outcomesWithSpace_safe_closed {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.seq first second) source).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.seq first second) source).2.safeForSpace = true)
    (firstOutcome : outcomesWithSpace64 conf secn label l1 l2 first source target locs)
    (firstCode : (DataSem.evaluate first source).2.code = source.code)
    (secondCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock ≤ source.clock →
      stateRel64 conf l1 l2 s t none locs →
      (DataSem.evaluate second s).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate second s).2.safeForSpace = true →
      outcomesWithSpace64 conf secn (compileControl64 conf secn label first).2 l1 l2 second s t locs) :
    outcomesWithSpace64 conf secn label l1 l2 (.seq first second) source target locs := by
  rcases firstOutcome with ordinary | failure
  · rcases ordinary with continued | returned | timeout | raised
    · obtain ⟨source', target', sourceRun, targetRun, afterFirst⟩ := continued
      let k := min source.clock source'.clock
      let sourceClamped := { source' with clock := k }
      let targetClamped := { target' with clock := k, termdep := target.termdep }
      have afterClamp : stateRel64 conf l1 l2 sourceClamped targetClamped none locs :=
        stateRel64_withClock conf l1 l2 source' target' none locs k afterFirst
      have sourceEq : DataSem.evaluate (.seq first second) source = DataSem.evaluate second sourceClamped := by
        simp [DataSem.evaluate, sourceRun, DataSem.fixClock, sourceClamped, k]
      have targetEq : WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.seq first second)).1 target =
          WordSemStateFiniteExact.evaluate (compileControl64 conf secn (compileControl64 conf secn label first).2 second).1 targetClamped := by
        have oldClock : target.clock = source.clock := related.2.1
        have newClock : target'.clock = source'.clock := afterFirst.2.1
        have minEq : (if source.clock < source'.clock then source.clock else source'.clock) = k := by
          dsimp [k]
          split <;> omega
        simp [compileControl64_seq, WordSemStateFiniteExact.evaluate, targetRun,
          WordSemStateFiniteExact.fixClock, oldClock, newClock, minEq, targetClamped]
      have secondSafe : (DataSem.evaluate second sourceClamped).1 ≠ some (.err (.abort .typeError)) := by
        simpa only [sourceEq] using safe
      have secondSpace : (DataSem.evaluate second sourceClamped).2.safeForSpace = true := by
        simpa only [sourceEq] using spaceSafe
      have codeEq : sourceClamped.code = source.code := by
        simpa [sourceRun, sourceClamped] using firstCode
      have clockBound : sourceClamped.clock ≤ source.clock := by
        simp [sourceClamped, k]
      rcases secondCorrect sourceClamped targetClamped codeEq clockBound afterClamp secondSafe secondSpace with ordinary | failure
      · left
        apply outcomes64_of_evaluations conf secn label (compileControl64 conf secn label first).2 l1 l2
          (.seq first second) second source sourceClamped target targetClamped locs sourceEq targetEq
        · intro a b next jump
          obtain ⟨mid, midJump⟩ := jumpExc_destination_of_keyEq target' targetClamped next a b
            (by exact of_eq_true (WordSemStackEq.sKeyEqRefl target'.stack)) rfl jump
          exact evaluate_continue_jumpExc_destination (compileControl64 conf secn label first).1 target target' mid a b targetRun midJump
        · exact ordinary
      · right
        obtain ⟨final, run, bound, events, unsafeProof⟩ := failure
        exact ⟨final, targetEq.trans run, by simpa [sourceEq] using bound,
          by simpa [sourceEq] using events, by simpa [sourceEq] using unsafeProof⟩
    · exact Or.inl (Or.inr (Or.inl (seq64_returnFirst conf secn label l1 l2 first second source target locs related returned)))
    · exact Or.inl (Or.inr (Or.inr (Or.inl (seq64_timeoutFirst conf secn label first second source target timeout))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (seq64_raiseFirst conf secn label l1 l2 first second source target locs related raised))))
  · exact Or.inr (seq64_outOfSpaceFirst conf secn label first second source target failure)

/-- Closed constructor-aware tail-call programs, including mutually recursive
calls, have an ordinary related outcome or permitted allocation failure.
This is a conditional Flapjack simulation, not unrestricted HOL correctness. -/
theorem tailConstructorFragment64 {C F : Type} (conf : Config) (program : DataLang.Prog)
    (fragment : TailConstructorFragment program) :
    ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
      (locs : List (Nat × Nat)), TailConstructorFragmentCode source.code →
      stateRel64 conf l1 l2 source target none locs →
      (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
      (DataSem.evaluate program source).2.safeForSpace = true →
      outcomesWithSpace64 conf secn label l1 l2 program source target locs := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), TailConstructorFragment program →
      ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
        (locs : List (Nat × Nat)), source.clock = clock → TailConstructorFragmentCode source.code →
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
        have firstCode := tailConstructorFragment_code first firstFrag source closed
        apply seq64_outcomesWithSpace_safe_closed conf secn label l1 l2 first second source target locs related safe spaceSafe
          firstOutcome firstCode
        intro s t codeEq bound rel valid space
        have nextClosed : TailConstructorFragmentCode s.code := by simpa [codeEq] using closed
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
              have nextClosed : TailConstructorFragmentCode (DataSem.callEnv values size (DataSem.decClock source)).code := by
                simpa [DataSem.callEnv, DataSem.decClock] using closed
              exact clockIH (DataSem.callEnv values size (DataSem.decClock source)).clock (by
                simp [DataSem.callEnv, DataSem.decClock]
                omega) body member callee 2 l1 l2 (DataSem.callEnv values size (DataSem.decClock source)) t locs
                rfl nextClosed rel valid space
  intro secn label l1 l2 source target locs closed related safe spaceSafe
  exact allClocks source.clock program fragment secn label l1 l2 source target locs rfl closed related safe spaceSafe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
