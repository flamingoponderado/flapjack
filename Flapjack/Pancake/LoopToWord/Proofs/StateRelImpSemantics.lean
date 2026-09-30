import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Assembly
import Flapjack.Pancake.CrepToLoop.Proofs.SemanticsWrapper
import Flapjack.Compiler.Backend.Semantics.WordSem.Semantics
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock
import Flapjack.Pancake.Semantics.LoopProps.EvaluateIoEventsExact
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact

/-!
# loop_to_word `state_rel_imp_semantics`, proof side

Proof-side counterpart of HOL `state_rel_imp_semantics`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:1538-1544`), bead
`flapjack-pxn.18.5.9.1`.  Both observational semantics are rewritten as the
`semantics_wrapper` of their clock-indexed entry runs: `loop_sem_is_wrapper`
for loopSem, and `wordSemIsWrapper` below for wordSem.  The equality then
follows from the tagged `semantics_wrapper_eq`.  Its premises come from:
* the tagged `compile_correct` at the entry `Call NONE (SOME start) [] NONE`
  (HOL's `comp_Call`);
* `evaluate_add_clock` for loopSem and wordSem;
* `evaluate_add_clock_io_events_mono` for loopSem and wordSem.

HOL proves the theorem by unfolding both `semantics_def`s directly.  This
module keeps HOL's statement and takes the proof route that the Crep-to-Loop
`state_rel_imp_semantics` port uses.  The wordSem
`evaluate_add_clock_io_events_mono` (bead `flapjack-pxn.18.5.9.1.3`) is
still the hypothesis `hwmono` here.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordStateRelImpSemanticsSupport

open Classical in
/-- The wordSem entry-run classification matching `wordSem$semantics_def`.
    HOL's `Fail` test covers `Exception`, `Result ret` with `ret ≠ Loc 1 0`,
    `Error` and `NONE`.  The termination cases are `FinalFFI`, `Result` and
    `NotEnoughSpace`.  `TimeOut`, `Break` and `Continue` are neither, so they
    are `Incomplete`.  Flapjack-specific: HOL states no wrapper for wordSem. -/
noncomputable def wordEntryClass {width : Nat} [NeZero width] :
    Option (WordSemResult width) → CrepToLoopSemanticsRunRes HolOutcome
  | some .timeOut => .Incomplete
  | some (.break _) => .Incomplete
  | some (.continue _) => .Incomplete
  | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
  | some (.result ret _) =>
      if ret = WordLocW.loc 1 0 then .CompleteResult HolOutcome.success else .RunError
  | some .notEnoughSpace => .CompleteResult HolOutcome.resourceLimitHit
  | _ => .RunError

open Classical in
private theorem wordSemIsWrapper_aux {width : Nat} [NeZero width] {C F : Type}
    (E : Nat → Option (WordSemResult width) × WordSemStateFiniteExact width C F) :
    (if ∃ k, (match (E k).1 with
        | some (.exception _ _) => True
        | some (.result ret _) => ret ≠ WordLocW.loc 1 0
        | some .error => True
        | none => True
        | _ => False)
      then HolBehaviour.fail
      else
        match holOptionSome (fun res => ∃ k t r outcome,
            E k = (r, t) ∧
            (match r with
             | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
             | some (.result _ _) => outcome = HolOutcome.success
             | some .notEnoughSpace => outcome = HolOutcome.resourceLimitHit
             | _ => False) ∧
            res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
        | some res => res
        | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
            l = HolLList.fromList (E k).2.ffi.ioEvents))) =
      crepToLoopSemanticsWrapper
        (Prod.map wordEntryClass
          (fun t : WordSemStateFiniteExact width C F => t.ffi.ioEvents) ∘ E) := by
  have hk : ∀ k, (match (E k).1 with
      | some (.exception _ _) => True
      | some (.result ret _) => ret ≠ WordLocW.loc 1 0
      | some .error => True
      | none => True
      | _ => False) ↔
      ∃ v, (Prod.map wordEntryClass
        (fun t : WordSemStateFiniteExact width C F => t.ffi.ioEvents) ∘ E) k = (.RunError, v) := by
    intro k
    simp only [Function.comp_apply]
    generalize E k = e
    rcases e with ⟨r, t⟩
    rcases r with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> simp [wordEntryClass]
  unfold crepToLoopSemanticsWrapper
  by_cases hf : ∃ k, (match (E k).1 with
      | some (.exception _ _) => True
      | some (.result ret _) => ret ≠ WordLocW.loc 1 0
      | some .error => True
      | none => True
      | _ => False)
  · rw [if_pos hf, if_pos ((exists_congr hk).1 hf)]
  · rw [if_neg hf, if_neg (fun h => hf ((exists_congr hk).2 h))]
    have hP : (fun res => ∃ k t r outcome,
        E k = (r, t) ∧
        (match r with
         | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
         | some (.result _ _) => outcome = HolOutcome.success
         | some .notEnoughSpace => outcome = HolOutcome.resourceLimitHit
         | _ => False) ∧
        res = HolBehaviour.terminate outcome t.ffi.ioEvents) =
        (fun res => ∃ k r ev,
          (Prod.map wordEntryClass
            (fun t : WordSemStateFiniteExact width C F => t.ffi.ioEvents) ∘ E) k =
            (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) := by
      funext res
      apply propext
      constructor
      · rintro ⟨k, t, r, outcome, he, hm, rfl⟩
        refine ⟨k, outcome, t.ffi.ioEvents, ?_, rfl⟩
        have hnf : ¬ (match (E k).1 with
            | some (.exception _ _) => True
            | some (.result ret _) => ret ≠ WordLocW.loc 1 0
            | some .error => True
            | none => True
            | _ => False) := fun h => hf ⟨k, h⟩
        simp only [Function.comp_apply, he, Prod.map] at hnf ⊢
        rcases r with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> simp at hm <;>
          simp_all [wordEntryClass]
      · rintro ⟨k, r', ev, hfk, rfl⟩
        simp only [Function.comp_apply] at hfk
        rcases he : E k with ⟨r, t⟩
        rw [he] at hfk
        simp only [Prod.map, Prod.mk.injEq] at hfk
        obtain ⟨hg, rfl⟩ := hfk
        refine ⟨k, t, r, r', he, ?_, rfl⟩
        rcases r with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> simp [wordEntryClass] at hg ⊢
        · split at hg
          · simp only [CrepToLoopSemanticsRunRes.CompleteResult.injEq] at hg
            exact hg.symm
          · exact absurd hg (by simp)
        · exact hg.symm
        · exact hg.symm
    rw [hP]
    rfl

/-- `wordSem$semantics_def` as the `semantics_wrapper` of its entry runs.
    Flapjack-specific: HOL has no wordSem analogue of `loop_sem_is_wrapper`. -/
theorem wordSemIsWrapper {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (start : Nat) :
    WordSemStateFiniteExact.semantics t start =
      crepToLoopSemanticsWrapper
        (Prod.map wordEntryClass
            (fun t : WordSemStateFiniteExact width C F => t.ffi.ioEvents) ∘
          (fun k => WordSemStateFiniteExact.evaluate
            (.call none (some start) [0] none : WordLangProgHOL (BitVec width))
            { t with clock := k })) := by
  unfold WordSemStateFiniteExact.semantics
  exact wordSemIsWrapper_aux _

/-- HOL `state_rel_imp_semantics` (`loop_to_wordProofScript.sml:1538-1544`),
    with the wordSem `evaluate_add_clock_io_events_mono` statement as the
    hypothesis `hwmono`.  The tagged theorem instantiates `hwmono` once bead
    `flapjack-pxn.18.5.9.1.3` lands.  Untagged for that reason only: the
    remaining binders, premises and conclusion are HOL's. -/
theorem stateRelImpSemantics_of_addClockIoEventsMono {width : Nat} [NeZero width] {C F : Type}
    (hwmono : ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (extra : Nat),
      (WordSemStateFiniteExact.evaluate p s).2.ffi.ioEvents <+:
        (WordSemStateFiniteExact.evaluate p { s with clock := s.clock + extra }).2.ffi.ioEvents) :
    ∀ (s : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (start : Nat),
      loopToWordStateRelHOLExact s t ∧ sptIsEmpty s.locals = true ∧ goodDimindex width ∧
        sptLookup 0 t.locals = some (WordLocW.loc 1 0) ∧
        (∃ prog : HolLoopProg width, sptLookup start s.code = some ([], prog)) ∧
        LoopSemStateFiniteExact.semantics s start ≠ .fail →
      WordSemStateFiniteExact.semantics t start = LoopSemStateFiniteExact.semantics s start := by
  intro s t start ⟨hsr, hemp, hdim, hret, _, hfail⟩
  have hloc : s.locals = .ln := by
    cases h : s.locals <;> simp_all [sptIsEmpty]
  have hfail' := hfail
  rw [loopSemIsWrapper] at hfail'
  rw [loopSemIsWrapper, wordSemIsWrapper]
  apply crepToLoopSemanticsWrapper_eq _ _ hfail'
  · -- Source runs are matched by target runs at the same clock (HOL `comp_Call`).
    intro k r ev habs hr
    simp only [Function.comp, Prod.map] at habs
    rcases hev : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none : HolLoopProg width)
        { s with clock := k } with ⟨res, s1⟩
    rw [hev] at habs
    simp only [Prod.mk.injEq] at habs
    obtain ⟨hcl, rfl⟩ := habs
    have hne : res ≠ some .error := by
      intro h
      subst h
      exact hr hcl.symm
    have hlocals : LoopToWord.localsRelHOL (makeCtxtHOL 2 [] .ln)
        ({ s with clock := k } : LoopSemStateFiniteExact width F).locals
        ({ t with clock := k } : WordSemStateFiniteExact width C F).locals := by
      show LoopToWord.localsRelHOL _ s.locals t.locals
      rw [hloc]
      exact LoopToWord.localsRelHOLMkCtxtLn 2 [] _ ⟨by decide, by decide⟩
    obtain ⟨t1, res1, hrun, hffi, hrc⟩ :=
      compileCorrect (C := C) (.call none (some start) [] none) { s with clock := k } res s1
        { t with clock := k } (makeCtxtHOL 2 [] .ln) (WordLocW.loc 1 0) (0, 0)
        ⟨hev, hne, loopToWordStateRelWithClockHOLExact s t k hsr, hlocals, hret, hdim,
          by simp [wordSemIsWordLoc], by intro x hx; simp [accVarsHOL, sptMem, sptDomain] at hx⟩
    refine ⟨0, ?_⟩
    have hcomp : (LoopToWord.compHOL (makeCtxtHOL 2 [] .ln)
        (.call none (some start) [] none : HolLoopProg width) (0, 0)).1 =
        .call none (some start) [0] none := by simp [LoopToWord.compHOL]
    rw [hcomp] at hrun
    simp only [Function.comp, Prod.map, Nat.add_zero]
    rw [hrun, hffi, ← hcl]
    refine Prod.ext ?_ rfl
    rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp only [resultCase] at hrc
    all_goals simp_all [wordEntryClass]
  · -- Target runs that complete are stable under more clock.
    intro k k' r ev hconc hr
    simp only [Function.comp, Prod.map] at hconc ⊢
    rcases hev : WordSemStateFiniteExact.evaluate
        (.call none (some start) [0] none : WordLangProgHOL (BitVec width))
        { t with clock := k } with ⟨res, st⟩
    rw [hev] at hconc
    simp only [Prod.mk.injEq] at hconc
    obtain ⟨hcl, rfl⟩ := hconc
    have hnt : res ≠ some .timeOut := by
      intro h
      subst h
      simp only [wordEntryClass] at hcl
      exact hr hcl.symm
    have hadd : WordSemStateFiniteExact.evaluate
        (.call none (some start) [0] none : WordLangProgHOL (BitVec width))
        { t with clock := k + k' } = (res, { st with clock := st.clock + k' }) :=
      WordSemStateFiniteExact.evaluate_add_clock k' _ { t with clock := k } res st ⟨hev, hnt⟩
    rw [hadd]
    exact Prod.ext hcl rfl
  · -- Source runs that complete are stable under more clock.
    intro k k' r ev habs hr
    simp only [Function.comp, Prod.map] at habs ⊢
    rcases hev : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none : HolLoopProg width)
        { s with clock := k } with ⟨res, st⟩
    rw [hev] at habs
    simp only [Prod.mk.injEq] at habs
    obtain ⟨hcl, rfl⟩ := habs
    have hnt : res ≠ some .timeOut := by
      intro h
      subst h
      exact hr hcl.symm
    have hadd : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none : HolLoopProg width)
        { s with clock := k + k' } = (res, { st with clock := st.clock + k' }) :=
      LoopSemStateFiniteExact.evaluate_add_clock_eq _ { s with clock := k } res st k' hev hnt
    rw [hadd]
    exact Prod.ext hcl rfl
  · -- Source traces grow with the clock.
    intro k k' ev habs
    refine ⟨_, _, rfl, ?_⟩
    have hev := (congrArg Prod.snd habs).symm
    simp only [Function.comp, Prod.map] at hev ⊢
    rw [hev]
    exact LoopSemStateFiniteExact.evaluate_add_clock_io_events_mono
      (.call none (some start) [] none) { s with clock := k } k'
  · -- Target traces grow with the clock.
    intro k k' ev hconc
    refine ⟨_, _, rfl, ?_⟩
    have hev := (congrArg Prod.snd hconc).symm
    simp only [Function.comp, Prod.map] at hev ⊢
    rw [hev]
    exact hwmono (.call none (some start) [0] none) { t with clock := k } k'

end LoopToWordStateRelImpSemanticsSupport

end Flapjack
