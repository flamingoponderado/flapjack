import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property

/-!
# Base control cases of `loop_to_word`'s `compile_correct`

These are the exact `loopSem$evaluate_ind` cases of HOL `compile_correct`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`) for the six
constructors resumed at `:533-563` and `:730-734`: `Skip`, `Fail`, `Tick`,
`Continue`, `Break` and `Mark`.  Bead `flapjack-pxn.18.5.9.21`.

Each theorem states HOL's goal written out for its constructor:
* the source evaluation and the non-`Error` premise;
* `state_rel`, `locals_rel`, `lookup 0 t.locals = SOME retv`,
  `good_dimindex`, `~isWord retv` and the `acc_vars` domain premise;
* the existential target run with the `ffi` equation and the result `case`
  (`resultCase`).

Of these constructors only `Mark` has an induction hypothesis: HOL's
`P (p, s)` for the body, rendered as `PropertyAt C p s`.  No target run or
post-state relation appears as a premise.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectBaseWitnesses

/-- Same-module roundtrip for the relation qualifier's loopSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module roundtrip for the relation qualifier's wordSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopToWordCompileCorrectBaseWitnesses

/-- Genuine `Skip` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:533-538`). There is no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Skip {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.skip) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.skip) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.skip) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, -, hState, hLocals, hRetv, -, -, -⟩
  simp only [LoopSemStateFiniteExact.evaluate, Prod.mk.injEq] at hEval
  obtain ⟨rfl, rfl⟩ := hEval
  refine ⟨t, none, by simp only [LoopToWord.compHOL]; rw [WordSemStateFiniteExact.evaluate], ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, hffi, _⟩ := hState; exact hffi
  · exact ⟨hState, rfl, hRetv, hLocals, rfl, rfl⟩

/-- Genuine `Fail` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:540-545`). There is no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Fail {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.fail) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.fail) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.fail) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNotError, -⟩
  simp only [LoopSemStateFiniteExact.evaluate, Prod.mk.injEq] at hEval
  exact absurd hEval.1.symm hNotError

/-- Genuine `Tick` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:547-556`). There is no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Tick {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.tick) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.tick) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.tick) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, -, hState, hLocals, hRetv, -, -, -⟩
  have hState' := hState
  obtain ⟨len, hmem, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  by_cases h0 : s.clock = 0
  · rw [if_pos h0, Prod.mk.injEq] at hEval
    obtain ⟨rfl, rfl⟩ := hEval
    refine ⟨WordSemStateFiniteExact.flushState true t, some .timeOut, ?_, ?_, rfl⟩
    · simp only [LoopToWord.compHOL]; rw [WordSemStateFiniteExact.evaluate]; simp [hclock, h0]
    · simp [WordSemStateFiniteExact.flushState, hffi]
  · rw [if_neg h0, Prod.mk.injEq] at hEval
    obtain ⟨rfl, rfl⟩ := hEval
    refine ⟨WordSemStateFiniteExact.decClock t, none, ?_, ?_, ?_⟩
    · simp only [LoopToWord.compHOL]; rw [WordSemStateFiniteExact.evaluate]; simp [hclock, h0]
    · simp [WordSemStateFiniteExact.decClock, LoopSemStateFiniteExact.decClock, hffi]
    · refine ⟨⟨len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, rfl, rfl⟩ <;>
        simp_all [WordSemStateFiniteExact.decClock, LoopSemStateFiniteExact.decClock]

/-- Genuine `Continue` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:559-562`). There is no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Continue {width : Nat} [NeZero width] {C F : Type}
    (k : Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.continue k) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ n, sptMem n (accVarsHOL (width := width) (.continue k) .ln) → sptMem n ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.continue k) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, -, hState, hLocals, hRetv, -, -, -⟩
  simp only [LoopSemStateFiniteExact.evaluate, Prod.mk.injEq] at hEval
  obtain ⟨rfl, rfl⟩ := hEval
  refine ⟨t, some (.continue k), by simp only [LoopToWord.compHOL]; rw [WordSemStateFiniteExact.evaluate], ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, hffi, _⟩ := hState; exact hffi
  · exact ⟨hState, rfl, hRetv, hLocals, rfl, rfl⟩

/-- Genuine `Break` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:565-568`). There is no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Break {width : Nat} [NeZero width] {C F : Type}
    (k : Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.break k) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ n, sptMem n (accVarsHOL (width := width) (.break k) .ln) → sptMem n ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.break k) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, -, hState, hLocals, hRetv, -, -, -⟩
  simp only [LoopSemStateFiniteExact.evaluate, Prod.mk.injEq] at hEval
  obtain ⟨rfl, rfl⟩ := hEval
  refine ⟨t, some (.break k), by simp only [LoopToWord.compHOL]; rw [WordSemStateFiniteExact.evaluate], ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, hffi, _⟩ := hState; exact hffi
  · exact ⟨hState, rfl, hRetv, hLocals, rfl, rfl⟩

/-- Genuine `Mark` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:730-734`). The induction hypothesis is HOL's `P (p, s)` for the body. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Mark {width : Nat} [NeZero width] {C F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (ih : PropertyAt C p s) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.mark p) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.mark p) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.mark p) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hGood, hWord, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  simp only [accVarsHOL] at hAcc
  simpa only [LoopToWord.compHOL] using ih res s1 t ctxt retv l
    ⟨hEval, hNE, hState, hLocals, hRetv, hGood, hWord, hAcc⟩

end Flapjack
