module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Induction
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.EvaluateMkLoc
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall
public import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock
public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock

@[expose] public section

/-! The `Seq` case of the data-to-word evaluator simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
namespace reviewedDataCompileCorrect_seqMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedDataCompileCorrect_seqMap

/-- The `Seq` case retains the complete conclusion of `data_compile_correct`.
Its hypotheses are the two evaluator induction hypotheses, including the
normal-result condition on the second program. The word evaluator inherits
the real-model assumption in `docs/SOUNDNESS.md` item 8. The full theorem
still requires assembly of all cases. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "data_compile_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem dataCompileCorrect_seq {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value)) (source1 : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (first second : Flapjack.Compiler.Backend.DataLang.Prog)
    (ihFirst : dataCompileCorrectInduction (width := width) first source)
    (ihSecond : ∀ r mid, (r, mid) = DataSem.evaluate first source ∧ r = none →
      dataCompileCorrectInduction (width := width) second mid)
    (run : DataSem.evaluate (.seq first second) source = (res, source1))
    (notTypeError : res ≠ some (.err (.abort .typeError)))
    (related : stateRel conf l1 l2 source target none locs)
    (_depth : target.termdep > 1) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.seq first second)).1 target = (res1, target1) ∧
      optionLe target1.stackMax source1.stackMax ∧
      (res1 = some .notEnoughSpace →
        target1.ffi.ioEvents.IsPrefix source1.ffi.ioEvents ∧
        (conf.gcKind ≠ .none → source1.safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        match res with
        | none => stateRel conf l1 l2 source1 target1 none locs ∧ res1 = none
        | some (.val values) =>
            ∃ words, words.length = values.length ∧
              stateRel conf l1 l2 source1 target1 (some (values.zip words)) locs ∧
              res1 = some (.result (.loc l1 l2) words)
        | some (.err (.raise value)) =>
            target1.ffi = source1.ffi ∧
            ∃ word l5 l6 rest,
              res1 = some (.exception (mkLoc (WordSemStateFiniteExact.jumpExc target)) word) ∧
              (WordSemStateFiniteExact.jumpExc target ≠ none →
                wordSemLastN (source1.stack.length + 1) locs = (l5, l6) :: rest ∧
                ∀ i, stateRel conf l5 l6 (DataSem.setVar i value source1)
                  (WordSemStateFiniteExact.setVar (adjustVar i) word target1) none rest)
        | some (.err (.abort (.ffiError event))) =>
            res1 = some (.finalFfi event) ∧ target1.ffi = source1.ffi
        | some (.err (.abort _)) => res1 = some .timeOut ∧ target1.ffi = source1.ffi) := by
  have compiled : (compileControl (width := width) conf n l (.seq first second)).1 =
      .seq (compileControl (width := width) conf n l first).1
        (compileControl (width := width) conf n (compileControl (width := width) conf n l first).2 second).1 := by
    have h := compileControl_option (width := width) conf n l (.seq first second)
    simp [compileControl?, compileControl_option] at h
    exact congrArg Prod.fst h.symm
  cases firstRun : DataSem.evaluate first source with
  | mk firstResult mid =>
    cases firstResult with
    | none =>
      have dataFix : DataSem.fixClock source
          ((none : Option (Result (List DataSem.Value) DataSem.Value)), mid) = (none, mid) := by
        simpa [firstRun] using DataSem.fixClockEvaluate source first
      have secondRun : DataSem.evaluate second mid = (res, source1) := by
        simpa [DataSem.evaluate, firstRun, dataFix] using run
      obtain ⟨targetMid, resultMid, targetFirst, firstBound, firstSpace, firstResult⟩ :=
        ihFirst conf n l l1 l2 none mid target locs firstRun (by simp) related _depth
      have clockFacts := WordSemStateFiniteExact.evaluate_clock _ _ _ _ targetFirst
      have targetFix : WordSemStateFiniteExact.fixClock target (resultMid, targetMid) = (resultMid, targetMid) := by
        simp [WordSemStateFiniteExact.fixClock, Nat.not_lt.mpr clockFacts.1, ← clockFacts.2]
      by_cases outOfSpace : resultMid = some .notEnoughSpace
      · have firstSpace' := firstSpace outOfSpace
        have events := DataSem.evaluate_events_of_result second mid res source1 secondRun
        have bound := DataSem.evaluate_stack_of_result second mid res source1 secondRun
        have targetFirst' : WordSemStateFiniteExact.evaluate (compileControl conf n l first).1 target =
            (some .notEnoughSpace, targetMid) := by simpa [outOfSpace] using targetFirst
        have targetFix' : WordSemStateFiniteExact.fixClock target
            (some (WordSemResult.notEnoughSpace : WordSemResult width), targetMid) =
            (some WordSemResult.notEnoughSpace, targetMid) := by simpa [outOfSpace] using targetFix
        refine ⟨targetMid, some .notEnoughSpace, ?_,
          optionLe_trans _ _ _ ⟨firstBound, bound⟩, ?_, ?_⟩
        · simp [compiled, WordSemStateFiniteExact.evaluate, targetFirst', targetFix']
        · intro _
          refine ⟨firstSpace'.1.trans events, ?_⟩
          intro gc
          have unsafeMid := firstSpace'.2 gc
          cases hsafe : source1.safeForSpace with
          | false => rfl
          | true =>
            have previous := DataSem.evaluate_safety_of_result second mid res source1 ⟨secondRun, hsafe⟩
            simp [unsafeMid] at previous
        · simp
      · have normal := firstResult outOfSpace
        have midRelated : stateRel conf l1 l2 mid targetMid none locs := normal.1
        have resultNone : resultMid = none := normal.2
        subst resultMid
        have depthMid : targetMid.termdep > 1 := by simpa [clockFacts.2] using _depth
        obtain ⟨target1, res1, targetSecond, stackBound, spaceFailure, result⟩ :=
          ihSecond none mid ⟨firstRun.symm, rfl⟩ conf n (compileControl (width := width) conf n l first).2
            l1 l2 res source1 targetMid locs secondRun notTypeError midRelated depthMid
        have locEq := evaluate_mkLoc _ _ _ targetFirst
        have jumpEq := evaluate_jumpExc_none_iff _ _ _ targetFirst
        refine ⟨target1, res1, ?_, stackBound, spaceFailure, ?_⟩
        · simp [compiled, WordSemStateFiniteExact.evaluate, targetFirst, targetFix, targetSecond]
        · intro hs
          have hr := result hs
          cases res with
          | none => exact hr
          | some r =>
            cases r with
            | val values => exact hr
            | err err =>
              cases err with
              | raise value => simpa [locEq, jumpEq] using hr
              | abort err => cases err <;> exact hr
    | some firstResult =>
      have dataFix : DataSem.fixClock source (some firstResult, mid) = (some firstResult, mid) := by
        simpa [firstRun] using DataSem.fixClockEvaluate source first
      have sourceEq : res = some firstResult ∧ source1 = mid := by
        simpa [DataSem.evaluate, firstRun, dataFix] using run.symm
      rcases sourceEq with ⟨resEq, sourceEq⟩
      subst res
      subst source1
      obtain ⟨targetMid, resultMid, targetFirst, firstBound, firstSpace, firstResultRel⟩ :=
        ihFirst conf n l l1 l2 (some firstResult) mid target locs firstRun notTypeError related _depth
      have clockFacts := WordSemStateFiniteExact.evaluate_clock _ _ _ _ targetFirst
      have targetFix : WordSemStateFiniteExact.fixClock target (resultMid, targetMid) = (resultMid, targetMid) := by
        simp [WordSemStateFiniteExact.fixClock, Nat.not_lt.mpr clockFacts.1, ← clockFacts.2]
      have nonempty : resultMid ≠ none := by
        intro empty
        have h := firstResultRel (by simp [empty])
        cases firstResult with
        | val values => simp [empty] at h
        | err err =>
          cases err with
          | raise value => simp [empty] at h
          | abort err => cases err <;> simp [empty] at h
      refine ⟨targetMid, resultMid, ?_, firstBound, firstSpace, ?_⟩
      · cases resultMid with
        | none => exact (nonempty rfl).elim
        | some r => simp [compiled, WordSemStateFiniteExact.evaluate, targetFirst, targetFix]
      · intro hs
        have h := firstResultRel hs
        cases firstResult with
        | val values => exact h
        | err err =>
          cases err with
          | raise value => exact h
          | abort err => cases err <;> exact h
end Flapjack.Compiler.Backend.DataToWord.Proofs
