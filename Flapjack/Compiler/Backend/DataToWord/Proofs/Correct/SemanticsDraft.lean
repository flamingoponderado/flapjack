module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CompileCorrectDraft
public import Flapjack.Compiler.Backend.Semantics.DataSem.Semantics
public import Flapjack.Compiler.Backend.Semantics.WordSem.Semantics
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClockIoEventsMono
public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateAddClock
public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateAddClockEvents
public import Flapjack.Compiler.Backend.Semantics.DataProps.CcCoOnlyDiffEval
public import Flapjack.SemanticsProps.Implements

@[expose] public section

/-! Observational layer of the data-to-word proof
(`data_to_wordProofScript.sml` lines 1305-1765: `compile_semantics_lemma`,
`compile_semantics_precise_lemma` and `compile_semantics_precise`), stated
over the clock-indexed entry-call families of `dataSem$semantics` and
`wordSem$semantics`. Every declaration here is Flapjack-local factoring of
those HOL proofs (HOL proves these steps inline) and has no separate HOL
declaration. The per-clock `EntrySim` is derived from the full statement of
`compile_correct` (`CompileCorrectStmt`), never assumed by a HOL-shaped
theorem; the `_of_assign` drafts obtain it from `compileCorrect_of_assign`,
i.e. modulo the not-yet-ported `Assign` case of `data_compile_correct`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.SemanticsDraft
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.BackendProps

/-- The full conclusion shape of HOL `compile_correct` (lines 1208-1289), as a
proposition about one fixed pair of carrier types. -/
def CompileCorrectStmt (width : Nat) [NeZero width] (C F : Type) : Prop :=
  ∀ (x : Flapjack.Compiler.Backend.DataToWord.Config) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value))
    (s1 : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (start : Nat),
    DataSem.evaluate (.call none (some start) [] none) s = (res, s1) ∧
      res ≠ some (.err (.abort .typeError)) ∧ stateRelExt x l1 l2 s t →
    ∃ ck t1 res1,
      WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        (WordSemStateFiniteExact.incClock ck t) = (res1, t1) ∧
      optionLe t1.stackMax s1.stackMax ∧
      (res1 = some .notEnoughSpace →
        t1.ffi.ioEvents.IsPrefix s1.ffi.ioEvents ∧ (x.gcKind ≠ .none → s1.safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        t1.ffi = s1.ffi ∧
        match res with
        | none => res1 = none
        | some (.val _) => ∃ w, res1 = some (.result (.loc l1 l2) w)
        | some (.err (.raise _)) => ∃ v w, res1 = some (.exception v w)
        | some (.err (.abort (.ffiError f))) => res1 = some (.finalFfi f)
        | some (.err (.abort _)) => res1 = some .timeOut)

/-- `compile_correct` modulo the `Assign` case. -/
theorem compileCorrectStmt_of_assign {width : Nat} [NeZero width] {C F : Type}
    (assignCase : ∀ (dest : Nat) (op : ClosLang.Op) (names : List Nat) (live : Option NumSet)
      (s : Flapjack.Compiler.Backend.DataSem.State C F),
      dataCompileCorrectInduction (width := width) (.assign dest op names live) s) :
    CompileCorrectStmt width C F :=
  fun x s l1 l2 res s1 t start h => by
    obtain ⟨ck, t1, res1, run, le, space, result⟩ :=
      compileCorrect_of_assign assignCase x s l1 l2 res s1 t start h
    refine ⟨ck, t1, res1, run, le, space, fun hn => ?_⟩
    have r := result hn
    rcases res with _ | (_ | (_ | (_ | _ | _))) <;> exact r

variable {width : Nat} [NeZero width] {C F : Type}

/-- The source entry call at a fixed clock. -/
noncomputable abbrev dataEntry (ffi : HolFfiState F) (code : Spt (Nat × DataLang.Prog))
    (co : DataSem.CompileOracle C) (cc : DataSem.Compiler C) (lims : DataSem.Limits)
    (fs : Spt Nat) (start k : Nat) :=
  DataSem.evaluate (.call none (some start) [] none)
    (DataSem.initialState ffi code co cc true lims fs k)

/-- The target entry call at a fixed clock. -/
noncomputable abbrev wordEntry (t : WordSemStateFiniteExact width C F) (start k : Nat) :=
  WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) {t with clock := k}

/-- Per-clock entry simulation: the conclusion of `compile_correct` at every
source clock. -/
def EntrySim (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ffi : HolFfiState F)
    (code : Spt (Nat × DataLang.Prog)) (co : DataSem.CompileOracle C) (cc : DataSem.Compiler C)
    (lims : DataSem.Limits) (fs : Spt Nat) (start : Nat) (t : WordSemStateFiniteExact width C F) :
    Prop :=
  ∀ k res s1, dataEntry ffi code co cc lims fs start k = (res, s1) →
    res ≠ some (.err (.abort .typeError)) →
    ∃ ck t1 res1, wordEntry t start (k + ck) = (res1, t1) ∧
      optionLe t1.stackMax s1.stackMax ∧
      (res1 = some .notEnoughSpace →
        t1.ffi.ioEvents.IsPrefix s1.ffi.ioEvents ∧ (conf.gcKind ≠ .none → s1.safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        t1.ffi = s1.ffi ∧
        match res with
        | none => res1 = none
        | some (.val _) => ∃ w, res1 = some (.result (.loc 1 0) w)
        | some (.err (.raise _)) => ∃ v w, res1 = some (.exception v w)
        | some (.err (.abort (.ffiError f))) => res1 = some (.finalFfi f)
        | some (.err (.abort _)) => res1 = some .timeOut)

/-- `compile_correct` at every clock, through `state_rel_ext_with_clock`. -/
theorem entrySim_of_compileCorrect (compileCorrect : CompileCorrectStmt width C F)
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ffi : HolFfiState F)
    (code : Spt (Nat × DataLang.Prog)) (co : DataSem.CompileOracle C) (cc : DataSem.Compiler C)
    (lims : DataSem.Limits) (start : Nat) (t : WordSemStateFiniteExact width C F)
    (related : stateRelExt conf 1 0
      (DataSem.initialState ffi code co cc true lims t.stackSize t.clock) t) :
    EntrySim conf ffi code co cc lims t.stackSize start t := by
  intro k res s1 run notType
  have moved := stateRelExt_withClock conf 1 0 _ t k related
  obtain ⟨ck, t1, res1, wordRun, rest⟩ :=
    compileCorrect conf _ 1 0 res s1 {t with clock := k} start ⟨run, notType, moved⟩
  exact ⟨ck, t1, res1, wordRun, rest⟩

section Families
variable (ffi : HolFfiState F) (code : Spt (Nat × DataLang.Prog)) (co : DataSem.CompileOracle C)
  (cc : DataSem.Compiler C) (lims : DataSem.Limits) (fs : Spt Nat) (start : Nat)

/-- A source entry result allowed by the dataSem fail guard. -/
theorem dataResultCases (notFail : DataSem.semantics ffi code co cc lims fs start ≠ .fail)
    (k : Nat) :
    (∃ v, (dataEntry ffi code co cc lims fs start k).1 = some (.val v)) ∨
      (dataEntry ffi code co cc lims fs start k).1 = some (.err (.abort .timeoutError)) ∨
      ∃ f, (dataEntry ffi code co cc lims fs start k).1 = some (.err (.abort (.ffiError f))) := by
  rcases h : (dataEntry ffi code co cc lims fs start k).1 with _ | (v | (v | (_ | _ | f)))
  · refine absurd ?_ notFail
    unfold DataSem.semantics
    rw [if_pos ⟨k, by simp only [dataEntry] at h; rw [h]; trivial⟩]
  · exact Or.inl ⟨v, rfl⟩
  · refine absurd ?_ notFail
    unfold DataSem.semantics
    rw [if_pos ⟨k, by simp only [dataEntry] at h; rw [h]; simp⟩]
  · refine absurd ?_ notFail
    unfold DataSem.semantics
    rw [if_pos ⟨k, by simp only [dataEntry] at h; rw [h]; simp⟩]
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨f, rfl⟩)

theorem dataNotTypeError (notFail : DataSem.semantics ffi code co cc lims fs start ≠ .fail)
    (k : Nat) : (dataEntry ffi code co cc lims fs start k).1 ≠ some (.err (.abort .typeError)) := by
  rcases dataResultCases ffi code co cc lims fs start notFail k with ⟨v, h⟩ | h | ⟨f, h⟩ <;>
    rw [h] <;> simp

theorem dataEntryAddClock (k extra : Nat)
    (res : Option (Result (List DataSem.Value) DataSem.Value)) (s1 : DataSem.State C F)
    (run : dataEntry ffi code co cc lims fs start k = (res, s1))
    (notTimeOut : res ≠ some (.err (.abort .timeoutError))) :
    dataEntry ffi code co cc lims fs start (k + extra) = (res, {s1 with clock := s1.clock + extra}) :=
  DataProps.evaluate_add_clock _ _ res s1 ⟨run, notTimeOut⟩ extra

theorem dataEntryEventsMono (k1 k2 : Nat) (le : k1 ≤ k2) :
    (dataEntry ffi code co cc lims fs start k1).2.ffi.ioEvents <+:
      (dataEntry ffi code co cc lims fs start k2).2.ffi.ioEvents := by
  have h := DataProps.evaluate_add_clock_io_events_mono (.call none (some start) [] none)
    (DataSem.initialState ffi code co cc true lims fs k1) (k2 - k1)
  simpa only [dataEntry, DataSem.initialState, Nat.add_sub_of_le le] using h

/-- The exact source termination-choice predicate of dataSem semantics. -/
abbrev dataTermination := DataSem.terminatingObservation ffi code co cc lims fs start

/-- The source clock family of divergent semantics. -/
def dataFamily (l : HolLList HolIoEvent) : Prop :=
  ∃ k, l = HolLList.fromList (dataEntry ffi code co cc lims fs start k).2.ffi.ioEvents

theorem dataSemanticsEq (notFail : DataSem.semantics ffi code co cc lims fs start ≠ .fail) :
    DataSem.semantics ffi code co cc lims fs start =
      match holOptionSome (dataTermination ffi code co cc lims fs start) with
      | some res => res
      | none => .diverge (HolLList.buildLprefixLub (dataFamily ffi code co cc lims fs start)) := by
  have notFail' := notFail
  unfold DataSem.semantics at notFail' ⊢
  dsimp only at notFail' ⊢
  split
  · rename_i bad
    exact absurd (if_pos bad) notFail'
  · rfl

theorem dataTerminationUnique (b1 b2 : HolBehaviour)
    (h1 : dataTermination ffi code co cc lims fs start b1)
    (h2 : dataTermination ffi code co cc lims fs start b2) : b2 = b1 := by
  obtain ⟨k1, t1, r1, o1, run1, m1, rfl⟩ := h1
  obtain ⟨k2, t2, r2, o2, run2, m2, rfl⟩ := h2
  wlog le : k1 ≤ k2 generalizing k1 t1 r1 o1 k2 t2 r2 o2
  · exact (this k2 t2 r2 o2 run2 m2 k1 t1 r1 o1 run1 m1 (by omega)).symm
  have notTimeOut : some r1 ≠ some (.err (.abort .timeoutError) :
      Result (List DataSem.Value) DataSem.Value) := by
    rintro ⟨⟩
    exact m1
  have boosted := dataEntryAddClock ffi code co cc lims fs start k1 (k2 - k1) (some r1) t1 run1
    notTimeOut
  rw [Nat.add_sub_of_le le] at boosted
  rw [dataEntry, run2] at boosted
  obtain ⟨sameResult, samePost⟩ := Prod.mk.inj boosted
  cases sameResult
  subst samePost
  rcases r1 with _ | (_ | (_ | (_ | _ | _))) <;> simp_all

theorem dataFamilyChain : HolLList.lprefixChain (dataFamily ffi code co cc lims fs start) := by
  rintro first second ⟨⟨k1, rfl⟩, ⟨k2, rfl⟩⟩
  rcases Nat.le_total k1 k2 with le | le
  · exact Or.inl ((HolLList.lprefix_fromList _ _).mpr
      (dataEntryEventsMono ffi code co cc lims fs start k1 k2 le))
  · exact Or.inr ((HolLList.lprefix_fromList _ _).mpr
      (dataEntryEventsMono ffi code co cc lims fs start k2 k1 le))

end Families

section WordFamilies
variable (t : WordSemStateFiniteExact width C F) (start : Nat)

theorem wordEntryAddClock (k extra : Nat) (res : Option (WordSemResult width))
    (t1 : WordSemStateFiniteExact width C F)
    (run : wordEntry t start k = (res, t1)) (notTimeOut : res ≠ some .timeOut) :
    wordEntry t start (k + extra) = (res, {t1 with clock := t1.clock + extra}) := by
  have h := WordSemStateFiniteExact.evaluate_add_clock extra _ _ res t1 ⟨run, notTimeOut⟩
  simpa only [wordEntry] using h

theorem wordEntryEventsMono (k1 k2 : Nat) (le : k1 ≤ k2) :
    (wordEntry t start k1).2.ffi.ioEvents <+: (wordEntry t start k2).2.ffi.ioEvents := by
  have h := WordSemStateFiniteExact.evaluate_add_clock_io_events_mono
    (.call none (some start) [0] none) {t with clock := k1} (k2 - k1)
  simpa only [wordEntry, Nat.add_sub_of_le le] using h

/-- Target results excluded by the wordSem fail guard. -/
def wordBad (r : Option (WordSemResult width)) : Prop :=
  match r with
  | some (.exception _ _) => True
  | some (.result ret _) => ret ≠ WordLocW.loc 1 0
  | some .error => True
  | none => True
  | _ => False

/-- The exact target termination-choice predicate of wordSem semantics. -/
def wordTermination (b : HolBehaviour) : Prop :=
  ∃ k t' r outcome,
    WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) {t with clock := k} =
      (r, t') ∧
    (match r with
     | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
     | some (.result _ _) => outcome = HolOutcome.success
     | some .notEnoughSpace => outcome = HolOutcome.resourceLimitHit
     | _ => False) ∧
    b = HolBehaviour.terminate outcome t'.ffi.ioEvents

/-- The target clock family of divergent semantics. -/
def wordFamily (l : HolLList HolIoEvent) : Prop :=
  ∃ k, l = HolLList.fromList (wordEntry t start k).2.ffi.ioEvents

theorem wordSemanticsEq (notBad : ∀ k, ¬ wordBad (wordEntry t start k).1) :
    WordSemStateFiniteExact.semantics t start =
      match holOptionSome (wordTermination t start) with
      | some res => res
      | none => .diverge (HolLList.buildLprefixLub (wordFamily t start)) := by
  unfold WordSemStateFiniteExact.semantics
  dsimp only
  split
  · rename_i bad
    obtain ⟨k, hk⟩ := bad
    exact absurd hk (notBad k)
  · rfl

theorem wordFamilyChain : HolLList.lprefixChain (wordFamily t start) := by
  rintro first second ⟨⟨k1, rfl⟩, ⟨k2, rfl⟩⟩
  rcases Nat.le_total k1 k2 with le | le
  · exact Or.inl ((HolLList.lprefix_fromList _ _).mpr (wordEntryEventsMono t start k1 k2 le))
  · exact Or.inr ((HolLList.lprefix_fromList _ _).mpr (wordEntryEventsMono t start k2 k1 le))

end WordFamilies

section Simulation
variable (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ffi : HolFfiState F)
  (code : Spt (Nat × DataLang.Prog)) (co : DataSem.CompileOracle C) (cc : DataSem.Compiler C)
  (lims : DataSem.Limits) (fs : Spt Nat) (start : Nat) (t : WordSemStateFiniteExact width C F)

/-- Target entry runs that are not time-outs agree with the source run of the
same clock: either a resource-limit stop on a source-trace prefix, or the
corresponding termination with the same FFI state. -/
theorem wordAgrees (sim : EntrySim conf ffi code co cc lims fs start t)
    (notFail : DataSem.semantics ffi code co cc lims fs start ≠ .fail)
    (k : Nat) (r : Option (WordSemResult width)) (t' : WordSemStateFiniteExact width C F)
    (run : wordEntry t start k = (r, t')) (notTimeOut : r ≠ some .timeOut) :
    ∃ res s1, dataEntry ffi code co cc lims fs start k = (res, s1) ∧
      (r = some .notEnoughSpace →
        t'.ffi.ioEvents <+: s1.ffi.ioEvents ∧ (conf.gcKind ≠ .none → s1.safeForSpace = false)) ∧
      (r ≠ some .notEnoughSpace → t'.ffi = s1.ffi ∧
        ((∃ v w, res = some (.val v) ∧ r = some (.result (.loc 1 0) w)) ∨
          ∃ f, res = some (.err (.abort (.ffiError f))) ∧ r = some (.finalFfi f))) := by
  rcases dataRun : dataEntry ffi code co cc lims fs start k with ⟨res, s1⟩
  have cases := dataResultCases ffi code co cc lims fs start notFail k
  have notType := dataNotTypeError ffi code co cc lims fs start notFail k
  rw [dataRun] at cases notType
  obtain ⟨ck, t1, res1, simRun, -, space, result⟩ := sim k res s1 dataRun notType
  have boosted := wordEntryAddClock t start k ck r t' run notTimeOut
  rw [simRun] at boosted
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj boosted
  refine ⟨res, s1, rfl, space, fun hn => ?_⟩
  obtain ⟨hffi, m⟩ := result hn
  refine ⟨hffi, ?_⟩
  rcases cases with ⟨v, rfl⟩ | rfl | ⟨f, rfl⟩
  · obtain ⟨w, hw⟩ := m
    exact Or.inl ⟨v, w, rfl, hw⟩
  · exact absurd m notTimeOut
  · exact Or.inr ⟨f, rfl, m⟩

theorem wordNotBad (sim : EntrySim conf ffi code co cc lims fs start t)
    (notFail : DataSem.semantics ffi code co cc lims fs start ≠ .fail) (k : Nat) :
    ¬ wordBad (wordEntry t start k).1 := by
  rcases run : wordEntry t start k with ⟨r, t'⟩
  by_cases hto : r = some .timeOut
  · subst hto
    simp [wordBad]
  by_cases hn : r = some .notEnoughSpace
  · subst hn
    simp [wordBad]
  obtain ⟨res, s1, -, -, result⟩ := wordAgrees conf ffi code co cc lims fs start t sim notFail k r t'
    run hto
  rcases (result hn).2 with ⟨v, w, -, rfl⟩ | ⟨f, -, rfl⟩ <;> simp [wordBad]

/-- A data termination at clock `k` agreeing with the target run at `k` with
the same FFI state is the source semantics. -/
theorem dataSameTermination (notFail : DataSem.semantics ffi code co cc lims fs start ≠ .fail)
    (k : Nat) (res : Option (Result (List DataSem.Value) DataSem.Value)) (s1 : DataSem.State C F)
    (dataRun : dataEntry ffi code co cc lims fs start k = (res, s1)) (r : Option (WordSemResult width))
    (o : HolOutcome)
    (m : match r, o with
      | some (.finalFfi e), outcome => outcome = HolOutcome.ffiOutcome e
      | some (.result _ _), outcome => outcome = HolOutcome.success
      | some .notEnoughSpace, outcome => outcome = HolOutcome.resourceLimitHit
      | _, _ => False)
    (same : (∃ v w, res = some (.val v) ∧ r = some (.result (.loc 1 0) w)) ∨
      ∃ f, res = some (.err (.abort (.ffiError f))) ∧ r = some (.finalFfi f)) :
    HolBehaviour.terminate o s1.ffi.ioEvents = DataSem.semantics ffi code co cc lims fs start := by
  have witness : dataTermination ffi code co cc lims fs start (.terminate o s1.ffi.ioEvents) := by
    rcases same with ⟨v, w, rfl, rfl⟩ | ⟨f, rfl, rfl⟩
    · exact ⟨k, s1, _, o, dataRun, m, rfl⟩
    · exact ⟨k, s1, _, o, dataRun, m, rfl⟩
  rw [dataSemanticsEq ffi code co cc lims fs start notFail,
    HolLList.holOptionSome_eq_some witness
      (dataTerminationUnique ffi code co cc lims fs start _ · witness)]

private theorem holOptionSome_eq_none' {α : Type} {P : α → Prop} (h : ∀ x, ¬ P x) :
    holOptionSome P = none := by
  unfold holOptionSome
  rw [dif_neg (fun ⟨x, hx⟩ => h x hx)]

/-- When the target has no termination witness, the source diverges with the
same trace limit. -/
theorem divergentEq (sim : EntrySim conf ffi code co cc lims fs start t)
    (notFail : DataSem.semantics ffi code co cc lims fs start ≠ .fail)
    (noTarget : ∀ b, ¬ wordTermination t start b) :
    HolBehaviour.diverge (HolLList.buildLprefixLub (wordFamily t start)) =
      DataSem.semantics ffi code co cc lims fs start := by
  have noSource : ∀ b, ¬ dataTermination ffi code co cc lims fs start b := by
    rintro b ⟨k2, s2, r2, o2, run2, m2, rfl⟩
    have notType2 := dataNotTypeError ffi code co cc lims fs start notFail k2
    rw [dataEntry, run2] at notType2
    obtain ⟨ck2, t2, res2, simRun2, -, -, result2⟩ := sim k2 _ s2 run2 notType2
    by_cases hn2 : res2 = some .notEnoughSpace
    · subst hn2
      exact noTarget _ ⟨k2 + ck2, t2, _, _, simRun2, rfl, rfl⟩
    obtain ⟨-, m⟩ := result2 hn2
    rcases r2 with v | (_ | (_ | _ | f))
    · obtain ⟨w, rfl⟩ := m
      exact noTarget _ ⟨k2 + ck2, t2, _, _, simRun2, rfl, rfl⟩
    · exact m2.elim
    · exact m2.elim
    · exact m2.elim
    · rw [m] at simRun2
      exact noTarget _ ⟨k2 + ck2, t2, _, _, simRun2, rfl, rfl⟩
  -- every source run is matched by an event-equal target run
  have matched : ∀ k, ∃ ck, (dataEntry ffi code co cc lims fs start k).2.ffi.ioEvents =
      (wordEntry t start (k + ck)).2.ffi.ioEvents := by
    intro k
    rcases run : dataEntry ffi code co cc lims fs start k with ⟨res, s1⟩
    have notType := dataNotTypeError ffi code co cc lims fs start notFail k
    rw [run] at notType
    obtain ⟨ck, t1, res1, simRun, -, -, result⟩ := sim k res s1 run notType
    by_cases hn : res1 = some .notEnoughSpace
    · subst hn
      exact (noTarget _ ⟨k + ck, t1, _, _, simRun, rfl, rfl⟩).elim
    refine ⟨ck, ?_⟩
    rw [simRun]
    exact congrArg (fun f => HolFfiState.ioEvents f) (result hn).1.symm
  rw [dataSemanticsEq ffi code co cc lims fs start notFail, holOptionSome_eq_none' noSource]
  dsimp only
  congr 1
  apply HolLList.IMP_build_lprefix_lub_EQ (wordFamilyChain t start)
    (dataFamilyChain ffi code co cc lims fs start)
  · rintro l ⟨k, rfl⟩
    obtain ⟨ck, eq⟩ := matched k
    refine ⟨_, ⟨k, rfl⟩, (HolLList.lprefix_fromList _ _).mpr ?_⟩
    rw [eq]
    exact wordEntryEventsMono t start k (k + ck) (Nat.le_add_right k ck)
  · rintro l ⟨k, rfl⟩
    obtain ⟨ck, eq⟩ := matched k
    refine ⟨_, ⟨k + ck, rfl⟩, (HolLList.lprefix_fromList _ _).mpr ?_⟩
    rw [eq]

/-- Membership of the target semantics in the resource-limit extension of the
source semantics, from the per-clock entry simulation. Local factoring of
HOL `compile_semantics_lemma`. -/
theorem semanticsOfEntrySim (sim : EntrySim conf ffi code co cc lims fs start t)
    (notFail : DataSem.semantics ffi code co cc lims fs start ≠ .fail) :
    SemanticsPropsHOL.extendWithResourceLimitHOL
      (fun b => b = DataSem.semantics ffi code co cc lims fs start)
      (WordSemStateFiniteExact.semantics t start) := by
  rw [wordSemanticsEq t start (wordNotBad conf ffi code co cc lims fs start t sim notFail)]
  rcases ht : holOptionSome (wordTermination t start) with _ | b
  · exact Or.inl (divergentEq conf ffi code co cc lims fs start t sim notFail (holOptionSome_none ht))
  · obtain ⟨k, t', r, o, targetRun, m, rfl⟩ := holOptionSome_some ht
    have notTimeOut : r ≠ some .timeOut := by
      rintro rfl
      exact m
    obtain ⟨res, s1, dataRun, space, result⟩ :=
      wordAgrees conf ffi code co cc lims fs start t sim notFail k r t' targetRun notTimeOut
    by_cases hn : r = some .notEnoughSpace
    · subst hn
      have limit : o = HolOutcome.resourceLimitHit := m
      subst limit
      have prefix' := (space rfl).1
      right
      rw [dataSemanticsEq ffi code co cc lims fs start notFail]
      rcases hs : holOptionSome (dataTermination ffi code co cc lims fs start) with _ | b
      · right
        refine ⟨_, _, rfl, rfl, ?_⟩
        apply HolLList.lprefix_trans ((HolLList.lprefix_fromList _ _).mpr prefix')
        apply HolLList.buildLprefixLub_upper (dataFamilyChain ffi code co cc lims fs start)
        exact ⟨k, by rw [dataRun]⟩
      · left
        obtain ⟨k2, s2, r2, o2, run2, m2, rfl⟩ := holOptionSome_some hs
        refine ⟨_, o2, s2.ffi.ioEvents, rfl, rfl, prefix'.trans ?_⟩
        rcases Nat.le_total k k2 with le | le
        · have mono := dataEntryEventsMono ffi code co cc lims fs start k k2 le
          rw [dataRun] at mono
          simpa only [dataEntry, run2] using mono
        · have notTimeOut2 : some r2 ≠ some (.err (.abort .timeoutError) :
              Result (List DataSem.Value) DataSem.Value) := by
            rintro ⟨⟩
            exact m2
          have boosted := dataEntryAddClock ffi code co cc lims fs start k2 (k - k2) _ s2 run2
            notTimeOut2
          rw [Nat.add_sub_of_le le, dataRun] at boosted
          obtain ⟨-, rfl⟩ := Prod.mk.inj boosted
          exact List.prefix_refl _
    · obtain ⟨hffi, same⟩ := result hn
      left
      rw [hffi]
      exact dataSameTermination ffi code co cc lims fs start notFail k res s1 dataRun r o m same

/-- When no source run at any clock ends in an unsafe state and the
configuration has a garbage collector, the resource-limit branch is empty and
the two semantics coincide. Local factoring of HOL
`compile_semantics_precise_lemma`. -/
theorem semanticsEqOfEntrySim (sim : EntrySim conf ffi code co cc lims fs start t)
    (notFail : DataSem.semantics ffi code co cc lims fs start ≠ .fail)
    (gc : conf.gcKind ≠ .none)
    (safe : ∀ k, (dataEntry ffi code co cc lims fs start k).2.safeForSpace = true) :
    WordSemStateFiniteExact.semantics t start = DataSem.semantics ffi code co cc lims fs start := by
  rw [wordSemanticsEq t start (wordNotBad conf ffi code co cc lims fs start t sim notFail)]
  rcases ht : holOptionSome (wordTermination t start) with _ | b
  · exact divergentEq conf ffi code co cc lims fs start t sim notFail (holOptionSome_none ht)
  · obtain ⟨k, t', r, o, targetRun, m, rfl⟩ := holOptionSome_some ht
    have notTimeOut : r ≠ some .timeOut := by
      rintro rfl
      exact m
    obtain ⟨res, s1, dataRun, space, result⟩ :=
      wordAgrees conf ffi code co cc lims fs start t sim notFail k r t' targetRun notTimeOut
    by_cases hn : r = some .notEnoughSpace
    · have notSafe := (space hn).2 gc
      have := safe k
      rw [dataRun] at this
      simp [notSafe] at this
    · obtain ⟨hffi, same⟩ := result hn
      dsimp only
      rw [hffi]
      exact dataSameTermination ffi code co cc lims fs start notFail k res s1 dataRun r o m same

end Simulation

/-- `data_lang_safe_for_space` (stated with HOL's arbitrary unit-typed oracle
and compiler) gives safety of the run with the actual oracle and compiler at
every clock, by `evaluate_cc_co_only_diff`. -/
theorem safeAtEveryClock (ffi : HolFfiState F) (code : Spt (Nat × DataLang.Prog))
    (co : DataSem.CompileOracle C) (cc : DataSem.Compiler C) (lims : DataSem.Limits)
    (fs : Spt Nat) (start : Nat) (safe : DataSem.dataLangSafeForSpace ffi code lims fs start)
    (k : Nat) : (dataEntry ffi code co cc lims fs start k).2.safeForSpace = true := by
  have hk := safe k
  rcases run : DataSem.evaluate (.call none (some start) [] none)
      (DataSem.initialState ffi code
        (@holArb (DataSem.CompileOracle Unit) ⟨fun _ => ((), [])⟩)
        (@holArb (DataSem.Compiler Unit) ⟨fun _ _ => none⟩) true lims fs k) with ⟨res, s1⟩
  rw [run] at hk
  obtain ⟨t1, run1, diff⟩ := DataProps.evaluate_cc_co_only_diff _ _ res s1
    (DataSem.initialState ffi code co cc true lims fs k)
    ⟨run, hk, by simp [DataProps.ccCoOnlyDiff, DataSem.initialState]⟩
  simp only [dataEntry, run1]
  rw [← diff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  exact hk

section Statements

/-- `compile_semantics_lemma` from the statement of `compile_correct`. -/
theorem compileSemanticsLemma_of_compileCorrect
    (compileCorrect : CompileCorrectStmt width C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ffi : HolFfiState F)
    (prog : List (Nat × Nat × DataLang.Prog)) (co : DataSem.CompileOracle C)
    (cc : DataSem.Compiler C) (lims : DataSem.Limits) (t : WordSemStateFiniteExact width C F)
    (fs : Spt Nat) (start : Nat)
    (h : stateRelExt conf 1 0
        (DataSem.initialState ffi (sptFromAList prog) co cc true lims t.stackSize t.clock) t ∧
      fs = t.stackSize ∧
      DataSem.semantics ffi (sptFromAList prog) co cc lims fs start ≠ .fail) :
    SemanticsPropsHOL.extendWithResourceLimitHOL
      (fun b => b = DataSem.semantics ffi (sptFromAList prog) co cc lims fs start)
      (WordSemStateFiniteExact.semantics t start) := by
  obtain ⟨related, rfl, notFail⟩ := h
  exact semanticsOfEntrySim conf ffi _ co cc lims _ start t
    (entrySim_of_compileCorrect compileCorrect conf ffi _ co cc lims start t related) notFail

/-- `compile_semantics_precise_lemma` from the statement of `compile_correct`. -/
theorem compileSemanticsPreciseLemma_of_compileCorrect
    (compileCorrect : CompileCorrectStmt width C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ffi : HolFfiState F)
    (prog : List (Nat × Nat × DataLang.Prog)) (co : DataSem.CompileOracle C)
    (cc : DataSem.Compiler C) (lims : DataSem.Limits) (t : WordSemStateFiniteExact width C F)
    (fs : Spt Nat) (start : Nat)
    (h : stateRelExt conf 1 0
        (DataSem.initialState ffi (sptFromAList prog) co cc true lims t.stackSize t.clock) t ∧
      fs = t.stackSize ∧
      DataSem.dataLangSafeForSpace ffi (sptFromAList prog) lims fs start ∧
      conf.gcKind ≠ .none ∧
      DataSem.semantics ffi (sptFromAList prog) co cc lims fs start ≠ .fail) :
    SemanticsPropsHOL.extendWithResourceLimitPrimeHOL true
      (fun b => b = DataSem.semantics ffi (sptFromAList prog) co cc lims fs start)
      (WordSemStateFiniteExact.semantics t start) := by
  obtain ⟨related, rfl, safe, gc, notFail⟩ := h
  simp only [SemanticsPropsHOL.extendWithResourceLimitPrimeHOL, if_true]
  exact semanticsEqOfEntrySim conf ffi _ co cc lims _ start t
    (entrySim_of_compileCorrect compileCorrect conf ffi _ co cc lims start t related) notFail gc
    (safeAtEveryClock ffi _ co cc lims _ start safe)

/-- `compile_semantics_precise` from the statement of `compile_correct`. -/
theorem compileSemanticsPrecise_of_compileCorrect
    (compileCorrect : CompileCorrectStmt width C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ffi : HolFfiState F)
    (prog : List (Nat × Nat × DataLang.Prog)) (co : DataSem.CompileOracle C)
    (cc : DataSem.Compiler C) (lims : DataSem.Limits) (t : WordSemStateFiniteExact width C F)
    (fs : Spt Nat) (start : Nat)
    (h : stateRelExt conf 1 0
        (DataSem.initialState ffi (sptFromAList prog) co cc true lims t.stackSize t.clock) t ∧
      fs = t.stackSize ∧ conf.gcKind ≠ .none ∧
      DataSem.semantics ffi (sptFromAList prog) co cc lims fs start ≠ .fail ∧
      DataSem.dataLangSafeForSpace ffi (sptFromAList prog) lims fs start) :
    WordSemStateFiniteExact.semantics t start =
      DataSem.semantics ffi (sptFromAList prog) co cc lims fs start := by
  obtain ⟨related, hfs, gc, notFail, safe⟩ := h
  have := compileSemanticsPreciseLemma_of_compileCorrect compileCorrect conf ffi prog co cc lims t fs
    start ⟨related, hfs, safe, gc, notFail⟩
  simpa only [SemanticsPropsHOL.extendWithResourceLimitPrimeHOL, if_true] using this

end Statements

end Flapjack.Compiler.Backend.DataToWord.Proofs.SemanticsDraft
