import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectHandlerCallSpace

/-! Recursive direct calls composed with allocation-space checks. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Allocation-capable commands and direct calls, closed under sequencing,
conditionals, local handler bodies, and indirect calls. Allocation-producing
primitives remain outside this fragment. -/
inductive DirectCallSpaceFragment : DataLang.Prog → Prop where
  | base {program : DataLang.Prog} : VerifiedWithSpace program → DirectCallSpaceFragment program
  | seq {first second : DataLang.Prog} : DirectCallSpaceFragment first → DirectCallSpaceFragment second →
      DirectCallSpaceFragment (.seq first second)
  | ite (name : Nat) {yes no : DataLang.Prog} : DirectCallSpaceFragment yes → DirectCallSpaceFragment no →
      DirectCallSpaceFragment (.ifThenElse name yes no)
  | tailCall (callee : Nat) (names : List Nat) : DirectCallSpaceFragment (.call none (some callee) names none)
  | indirectTailCall (names : List Nat) : DirectCallSpaceFragment (.call none none names none)
  | returningCall (callee : Nat) (names returns : List Nat) (live : NumSet) :
      DirectCallSpaceFragment (.call (some (returns, live)) (some callee) names none)
  | indirectReturningCall (names returns : List Nat) (live : NumSet) :
      DirectCallSpaceFragment (.call (some (returns, live)) none names none)
  | handledCall (callee : Nat) (names returns : List Nat) (live : NumSet) (handlerName : Nat)
      {handlerBody : DataLang.Prog} : DirectCallSpaceFragment handlerBody →
      DirectCallSpaceFragment (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody)))
  | indirectHandledCall (names returns : List Nat) (live : NumSet) (handlerName : Nat)
      {handlerBody : DataLang.Prog} : DirectCallSpaceFragment handlerBody →
      DirectCallSpaceFragment (.call (some (returns, live)) none names (some (handlerName, handlerBody)))

/-- Every callable body in the code tree belongs to the direct-call and
allocation-space fragment. -/
def DirectCallSpaceFragmentCode (code : Spt (Nat × DataLang.Prog)) : Prop :=
  ∀ label arity body, sptLookup label code = some (arity, body) → DirectCallSpaceFragment body

/-- Executing a closed direct-call and allocation-space fragment preserves
its source code table, including recursive and mutually recursive calls. -/
theorem directCallSpaceFragment_code {C F : Type} (program : DataLang.Prog)
    (fragment : DirectCallSpaceFragment program) (state : DataSem.State C F)
    (closed : DirectCallSpaceFragmentCode state.code) : (DataSem.evaluate program state).2.code = state.code := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), DirectCallSpaceFragment program →
      ∀ state : DataSem.State C F, state.clock = clock → DirectCallSpaceFragmentCode state.code →
        (DataSem.evaluate program state).2.code = state.code := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro program fragment
      induction fragment with
      | base frag => intro state _ _; exact verifiedWithSpace_code _ frag state
      | @seq first second firstFrag secondFrag firstIH secondIH =>
        intro state eq closed
        apply DataSem.evaluate_seq_code_step first second state (firstIH state eq closed)
        intro mid codeEq clockBound
        have midClosed : DirectCallSpaceFragmentCode mid.code := by simpa [codeEq] using closed
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
          have nextClosed : DirectCallSpaceFragmentCode next.code := by simpa [codeEq] using closed
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
          have nextClosed : DirectCallSpaceFragmentCode next.code := by simpa [codeEq] using closed
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
          have nextClosed : DirectCallSpaceFragmentCode next.code := by simpa [codeEq] using closed
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
          have nextClosed : DirectCallSpaceFragmentCode next.code := by simpa [codeEq] using closed
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
          have nextClosed : DirectCallSpaceFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq next smaller codeEq
          cases handlerEq
          have nextClosed : DirectCallSpaceFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) handlerBody handlerFrag next rfl nextClosed).trans codeEq
      | @indirectHandledCall names returns live handlerName handlerBody handlerFrag handlerIH =>
        intro state eq closed
        apply DataSem.evaluate_call_code_step (some (returns, live)) none names (some (handlerName, handlerBody)) state
        · intro values args body size found next smaller codeEq
          obtain ⟨label, arity, lookup⟩ := findCode_body_lookup none values state.code
            state.stackFrameSizes args body size found
          have member := closed label arity body lookup
          have nextClosed : DirectCallSpaceFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq next smaller codeEq
          cases handlerEq
          have nextClosed : DirectCallSpaceFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) handlerBody handlerFrag next rfl nextClosed).trans codeEq
  exact allClocks state.clock program fragment state rfl closed

/-- Actual compiled execution of a closed direct-call and allocation-space
fragment has a related ordinary outcome or permitted allocation failure. The
clock induction includes recursive calls and frame restoration; this is not
unrestricted compiler correctness. -/
theorem directCallSpaceFragment64 {C F : Type} (conf : Config) (program : DataLang.Prog)
    (fragment : DirectCallSpaceFragment program) :
    ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
      (locs : List (Nat × Nat)), DirectCallSpaceFragmentCode source.code →
      stateRel64 conf l1 l2 source target none locs →
      (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
      outcomesWithSpace64 conf secn label l1 l2 program source target locs := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), DirectCallSpaceFragment program →
      ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
        (locs : List (Nat × Nat)), source.clock = clock → DirectCallSpaceFragmentCode source.code →
        stateRel64 conf l1 l2 source target none locs →
        (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
        outcomesWithSpace64 conf secn label l1 l2 program source target locs := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro program fragment
      induction fragment with
      | base frag =>
        intro secn label l1 l2 source target locs eq closed related safe
        exact verifiedWithSpace64 conf secn l1 l2 _ frag label source target locs related safe
      | @seq first second firstFrag secondFrag firstIH secondIH =>
        intro secn label l1 l2 source target locs eq closed related safe
        have firstOutcome := firstIH secn label l1 l2 source target locs eq closed related
          (seq_first_safe first second source safe)
        have firstCode := directCallSpaceFragment_code first firstFrag source closed
        apply seq64_outcomesWithSpace_closed conf secn label l1 l2 first second source target locs related safe
          firstOutcome firstCode
        intro s t codeEq bound rel valid
        have nextClosed : DirectCallSpaceFragmentCode s.code := by simpa [codeEq] using closed
        rcases Nat.lt_or_eq_of_le bound with less | same
        · exact clockIH s.clock (by omega) second secondFrag secn (compileControl64 conf secn label first).2
            l1 l2 s t locs rfl nextClosed rel valid
        · exact secondIH secn (compileControl64 conf secn label first).2 l1 l2 s t locs (by omega) nextClosed rel valid
      | @ite name yes no yesFrag noFrag yesIH noIH =>
        intro secn label l1 l2 source target locs eq closed related safe
        apply if64_outcomesWithSpace conf secn label l1 l2 name yes no source target locs related safe
        · intro valid
          exact yesIH secn label l1 l2 source target locs eq closed related valid
        · intro valid
          exact noIH secn (compileControl64 conf secn label yes).2 l1 l2 source target locs eq closed related valid
      | tailCall callee names =>
        intro secn label l1 l2 source target locs eq closed related safe
        apply tailCall64_direct_withSpace_of_safe conf secn label l1 l2 source target locs related callee names safe
        intro body args size found s t codeEq smaller rel valid
        obtain ⟨calleeLabel, arity, lookup⟩ := findCode_body_lookup (some callee) args source.code
          source.stackFrameSizes args body size found
        have member := closed calleeLabel arity body lookup
        have nextClosed : DirectCallSpaceFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 l1 l2 s t locs rfl nextClosed rel valid
      | indirectTailCall names =>
        intro secn label l1 l2 source target locs eq closed related safe
        apply tailCall64_indirect_withSpace_of_safe conf secn label l1 l2 source target locs related names safe
        intro callee arity body lookup s t codeEq smaller rel valid
        have member := closed callee arity body lookup
        have nextClosed : DirectCallSpaceFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 l1 l2 s t locs rfl nextClosed rel valid
      | returningCall callee names returns live =>
        intro secn label l1 l2 source target locs eq closed related safe
        apply call64_direct_noHandler_withSpace_of_safe conf secn label l1 l2 source target locs related callee names returns live safe
        intro body args size found s t codeEq smaller rel valid
        obtain ⟨calleeLabel, arity, lookup⟩ := findCode_body_lookup (some callee) args source.code
          source.stackFrameSizes args body size found
        have member := closed calleeLabel arity body lookup
        have nextClosed : DirectCallSpaceFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs) rfl nextClosed rel valid
      | indirectReturningCall names returns live =>
        intro secn label l1 l2 source target locs eq closed related safe
        apply call64_indirect_noHandler_withSpace_of_safe conf secn label l1 l2 source target locs related names returns live safe
        intro callee arity body lookup s t codeEq smaller rel valid
        have member := closed callee arity body lookup
        have nextClosed : DirectCallSpaceFragmentCode s.code := by simpa [codeEq] using closed
        exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs) rfl nextClosed rel valid
      | @handledCall callee names returns live handlerName handlerBody handlerFrag handlerIH =>
        intro secn label l1 l2 source target locs eq closed related safe
        apply call64_direct_handler_withSpace_of_safe conf secn label l1 l2 source target locs related
          callee names returns live handlerName handlerBody safe
        · intro body args size found s t codeEq smaller rel valid
          obtain ⟨calleeLabel, arity, lookup⟩ := findCode_body_lookup (some callee) args source.code
            source.stackFrameSizes args body size found
          have member := closed calleeLabel arity body lookup
          have nextClosed : DirectCallSpaceFragmentCode s.code := by simpa [codeEq] using closed
          exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs) rfl nextClosed rel valid
        · intro body args size saved found cut
          obtain ⟨calleeLabel, arity, lookup⟩ := findCode_body_lookup (some callee) args source.code
            source.stackFrameSizes args body size found
          have member := closed calleeLabel arity body lookup
          simpa [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using
            directCallSpaceFragment_code body member
              (DataSem.callEnv args size (DataSem.pushEnv saved true (DataSem.decClock source)))
              (by simpa [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using closed)
        · intro s t codeEq smaller rel valid
          have nextClosed : DirectCallSpaceFragmentCode s.code := by simpa [codeEq] using closed
          exact clockIH s.clock (by omega) handlerBody handlerFrag secn (label + 2) l1 l2 s t locs rfl nextClosed rel valid
      | @indirectHandledCall names returns live handlerName handlerBody handlerFrag handlerIH =>
        intro secn label l1 l2 source target locs eq closed related safe
        apply call64_indirect_handler_withSpace_of_safe conf secn label l1 l2 source target locs related
          names returns live handlerName handlerBody safe
        · intro callee arity body lookup s t codeEq smaller rel valid
          have member := closed callee arity body lookup
          have nextClosed : DirectCallSpaceFragmentCode s.code := by simpa [codeEq] using closed
          exact clockIH s.clock (by omega) body member callee 2 secn label s t ((l1, l2) :: locs) rfl nextClosed rel valid
        · intro callee arity body values saved lookup cut
          have member := closed callee arity body lookup
          simpa [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using
            directCallSpaceFragment_code body member
              (DataSem.callEnv values (sptLookup callee source.stackFrameSizes)
                (DataSem.pushEnv saved true (DataSem.decClock source)))
              (by simpa [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using closed)
        · intro s t codeEq smaller rel valid
          have nextClosed : DirectCallSpaceFragmentCode s.code := by simpa [codeEq] using closed
          exact clockIH s.clock (by omega) handlerBody handlerFrag secn (label + 2) l1 l2 s t locs rfl nextClosed rel valid
  intro secn label l1 l2 source target locs closed related safe
  exact allClocks source.clock program fragment secn label l1 l2 source target locs rfl closed related safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
