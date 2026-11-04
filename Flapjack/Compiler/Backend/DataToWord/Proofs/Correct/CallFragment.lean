import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CallFragmentCode
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectCaughtCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectUnhandledCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectTailCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CaughtCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.UnhandledCall

/-! Composition of data-to-word simulations for fragments containing calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Sequential execution composes all covered outcomes while respecting
clock clamping, code preservation, and restoration of termination depth. -/
theorem seq64_outcomes_closed {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (first second : DataLang.Prog) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.seq first second) source).1 ≠ some (.err (.abort .typeError)))
    (firstOutcome : outcomes64 conf secn label l1 l2 first source target locs)
    (firstCode : (DataSem.evaluate first source).2.code = source.code)
    (secondCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
      s.code = source.code → s.clock ≤ source.clock →
      stateRel64 conf l1 l2 s t none locs → (DataSem.evaluate second s).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf secn (compileControl64 conf secn label first).2 l1 l2 second s t locs) :
    outcomes64 conf secn label l1 l2 (.seq first second) source target locs := by
  rcases firstOutcome with continued | returned | timeout | raised
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
    have codeEq : sourceClamped.code = source.code := by
      simpa [sourceRun, sourceClamped] using firstCode
    have clockBound : sourceClamped.clock ≤ source.clock := by
      simp [sourceClamped, k]
    have secondSafe : (DataSem.evaluate second sourceClamped).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [sourceEq] using safe
    exact outcomes64_of_evaluations conf secn label (compileControl64 conf secn label first).2 l1 l2
      (.seq first second) second source sourceClamped target targetClamped locs sourceEq targetEq
      (by
        intro a b next jump
        obtain ⟨mid, midJump⟩ := jumpExc_destination_of_keyEq target' targetClamped next a b
          (by exact of_eq_true (WordSemStackEq.sKeyEqRefl target'.stack)) rfl jump
        exact evaluate_continue_jumpExc_destination (compileControl64 conf secn label first).1 target target' mid a b targetRun midJump)
      (secondCorrect sourceClamped targetClamped codeEq clockBound afterClamp secondSafe)
  · exact Or.inr (Or.inl (seq64_returnFirst conf secn label l1 l2 first second source target locs related returned))
  · exact Or.inr (Or.inr (Or.inl (seq64_timeoutFirst conf secn label first second source target timeout)))
  · exact Or.inr (Or.inr (Or.inr (seq64_raiseFirst conf secn label l1 l2 first second source target locs related raised)))

/-- Source-safe conditionals inherit one of the covered outcomes from the
branch selected by their related Boolean locals. -/
theorem if64_outcomes_at_state {C F : Type} (conf : Config) (secn label l1 l2 name : Nat)
    (yes no : DataLang.Prog) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (safe : (DataSem.evaluate (.ifThenElse name yes no) source).1 ≠ some (.err (.abort .typeError)))
    (yesCorrect : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf secn label l1 l2 yes source target locs)
    (noCorrect : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf secn (compileControl64 conf secn label yes).2 l1 l2 no source target locs) :
    outcomes64 conf secn label l1 l2 (.ifThenElse name yes no) source target locs := by
  obtain ⟨value, b, sourceRun, bool⟩ := if64_source_boolean source name yes no safe
  have branch := if64_branch conf secn label l1 l2 name yes no source target locs related value b sourceRun bool
  cases b with
  | false =>
    have branchSafe : (DataSem.evaluate no source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [Bool.false_eq_true, ↓reduceIte, branch.1] using safe
    apply outcomes64_of_evaluations conf secn label (compileControl64 conf secn label yes).2 l1 l2
      (.ifThenElse name yes no) no source source target target locs
    · simpa only [Bool.false_eq_true, ↓reduceIte] using branch.1
    · simpa only [Bool.false_eq_true, ↓reduceIte] using branch.2
    · intro a b next jump
      exact ⟨next, jump⟩
    · exact noCorrect branchSafe
  | true =>
    have branchSafe : (DataSem.evaluate yes source).1 ≠ some (.err (.abort .typeError)) := by
      simpa only [↓reduceIte, branch.1] using safe
    apply outcomes64_of_evaluations conf secn label label l1 l2
      (.ifThenElse name yes no) yes source source target target locs
    · simpa only [↓reduceIte] using branch.1
    · simpa only [↓reduceIte] using branch.2
    · intro a b next jump
      exact ⟨next, jump⟩
    · exact yesCorrect branchSafe

/-- Successful direct lookup identifies the body at the requested label. -/
theorem findCode_direct_body_lookup (callee : Nat) (args : List DataSem.Value)
    (code : Spt (Nat × DataLang.Prog)) (sizes : Spt Nat)
    (body : DataLang.Prog) (size : Option Nat)
    (found : DataSem.findCode (some callee) args code sizes = some (args, body, size)) :
    ∃ arity, sptLookup callee code = some (arity, body) := by
  cases entry : sptLookup callee code with
  | none => simp [DataSem.findCode, entry] at found
  | some pair =>
    obtain ⟨arity, prog⟩ := pair
    by_cases length : args.length = arity
    · simp [DataSem.findCode, entry, length] at found
      exact ⟨arity, by simp_all⟩
    · simp [DataSem.findCode, entry, length] at found

/-- Programs in the call-extended fragment are simulated when the source code
contains only bodies from that fragment. The induction covers recursive calls
using the source clock; the state relation and executable evaluators remain the
existing Lean candidates and this is not an unrestricted HOL theorem port. -/
theorem callFragment64 {C F : Type} (conf : Config) (program : DataLang.Prog)
    (fragment : CallFragment program) :
    ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
      (locs : List (Nat × Nat)), CallFragmentCode source.code →
      stateRel64 conf l1 l2 source target none locs →
      (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
      outcomes64 conf secn label l1 l2 program source target locs := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), CallFragment program →
      ∀ (secn label l1 l2 : Nat) (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
        (locs : List (Nat × Nat)), source.clock = clock → CallFragmentCode source.code →
        stateRel64 conf l1 l2 source target none locs →
        (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)) →
        outcomes64 conf secn label l1 l2 program source target locs := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro program fragment
      induction fragment with
      | base frag =>
        intro secn label l1 l2 source target locs eq closed related safe
        exact verifiedFragment64 conf secn l1 l2 _ frag label source target locs related safe
      | @seq first second firstFrag secondFrag firstIH secondIH =>
        intro secn label l1 l2 source target locs eq closed related safe
        have firstSafe := seq_first_safe first second source safe
        have firstOutcome := firstIH secn label l1 l2 source target locs eq closed related firstSafe
        have firstCode := callFragment_code first firstFrag source closed
        apply seq64_outcomes_closed conf secn label l1 l2 first second source target locs related safe firstOutcome firstCode
        intro s t codeEq bound rel valid
        have nextClosed : CallFragmentCode s.code := by simpa [codeEq] using closed
        rcases Nat.lt_or_eq_of_le bound with less | same
        · exact clockIH s.clock (by omega) second secondFrag secn (compileControl64 conf secn label first).2 l1 l2 s t locs rfl nextClosed rel valid
        · exact secondIH secn (compileControl64 conf secn label first).2 l1 l2 s t locs (by omega) nextClosed rel valid
      | @ite name yes no yesFrag noFrag yesIH noIH =>
        intro secn label l1 l2 source target locs eq closed related safe
        apply if64_outcomes_at_state conf secn label l1 l2 name yes no source target locs related safe
        · intro valid
          exact yesIH secn label l1 l2 source target locs eq closed related valid
        · intro valid
          exact noIH secn (compileControl64 conf secn label yes).2 l1 l2 source target locs eq closed related valid
      | @call ret dest names handler handlerFrag handlerIH =>
        intro secn label l1 l2 source target locs eq closed related safe
        have calleeIH : ∀ (callee arity : Nat) (body : DataLang.Prog),
            sptLookup callee source.code = some (arity, body) →
            ∀ (r1 r2 : Nat) (positions : List (Nat × Nat)) (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
              s.code = source.code → s.clock < source.clock → stateRel64 conf r1 r2 s t none positions →
              (DataSem.evaluate body s).1 ≠ some (.err (.abort .typeError)) →
              outcomes64 conf callee 2 r1 r2 body s t positions := by
          intro callee arity body lookup r1 r2 positions s t codeEq smaller rel valid
          have member := closed callee arity body lookup
          have nextClosed : CallFragmentCode s.code := by simpa [codeEq] using closed
          exact clockIH s.clock (by omega) body member callee 2 r1 r2 s t positions rfl nextClosed rel valid
        cases ret with
        | none =>
          cases handler with
          | some handler =>
            cases read : DataSem.getVars names source.locals with
            | none => simp [DataSem.evaluate, read] at safe
            | some values =>
              cases found : DataSem.findCode dest values source.code source.stackFrameSizes with
              | none => simp [DataSem.evaluate, read, found] at safe
              | some entry =>
                obtain ⟨args, body, size⟩ := entry
                simp [DataSem.evaluate, read, found] at safe
          | none =>
            cases dest with
            | none =>
              apply tailCall64_indirect_of_safe conf secn label l1 l2 source target locs related names safe
              intro callee arity body lookup
              exact calleeIH callee arity body lookup l1 l2 locs
            | some callee =>
              apply tailCall64_direct_of_safe conf secn label l1 l2 source target locs related callee names safe
              intro body args size found
              obtain ⟨arity, lookup⟩ := findCode_direct_body_lookup callee args source.code source.stackFrameSizes body size found
              exact calleeIH callee arity body lookup l1 l2 locs
        | some returnInfo =>
          obtain ⟨returns, live⟩ := returnInfo
          cases handler with
          | none =>
            cases dest with
            | none =>
              apply call64_indirect_noHandler_of_safe conf secn label l1 l2 source target locs related names returns live safe
              intro callee arity body lookup
              exact calleeIH callee arity body lookup secn label ((l1, l2) :: locs)
            | some callee =>
              apply call64_direct_noHandler_of_safe conf secn label l1 l2 source target locs related callee names returns live safe
              intro body args size found
              obtain ⟨arity, lookup⟩ := findCode_direct_body_lookup callee args source.code source.stackFrameSizes body size found
              exact calleeIH callee arity body lookup secn label ((l1, l2) :: locs)
          | some handler =>
            obtain ⟨handlerName, handlerBody⟩ := handler
            have handlerCorrect : ∀ (s : DataSem.State C F) (t : WordSemStateFiniteExact 64 C F),
                s.code = source.code → s.clock < source.clock → stateRel64 conf l1 l2 s t none locs →
                (DataSem.evaluate handlerBody s).1 ≠ some (.err (.abort .typeError)) →
                outcomes64 conf secn (label + 2) l1 l2 handlerBody s t locs := by
              intro s t codeEq smaller rel valid
              have nextClosed : CallFragmentCode s.code := by simpa [codeEq] using closed
              exact clockIH s.clock (by omega) handlerBody (handlerFrag handlerName handlerBody rfl)
                secn (label + 2) l1 l2 s t locs rfl nextClosed rel valid
            cases dest with
            | none =>
              apply call64_indirect_handler_of_safe conf secn label l1 l2 source target locs related names returns live handlerName handlerBody safe
              · intro callee arity body lookup
                exact calleeIH callee arity body lookup secn label ((l1, l2) :: locs)
              · exact closed
              · exact handlerCorrect
            | some callee =>
              apply call64_direct_handler_of_safe conf secn label l1 l2 source target locs related callee names returns live handlerName handlerBody safe
              · intro body args size found
                obtain ⟨arity, lookup⟩ := findCode_direct_body_lookup callee args source.code source.stackFrameSizes body size found
                exact calleeIH callee arity body lookup secn label ((l1, l2) :: locs)
              · exact closed
              · exact handlerCorrect
  intro secn label l1 l2 source target locs closed related safe
  exact allClocks source.clock program fragment secn label l1 l2 source target locs rfl closed related safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
