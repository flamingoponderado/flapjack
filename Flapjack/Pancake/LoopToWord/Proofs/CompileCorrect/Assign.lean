import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property
import Flapjack.Pancake.Proofs.LoopToWord.CompExpPreservesEval
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelUpdates
import Flapjack.Pancake.Proofs.LoopToWord.FindVar

/-!
# `Assign`, `LocValue` and `SetGlobal` cases of `loop_to_word`'s `compile_correct`

These are the exact `loopSem$evaluate_ind` cases of HOL `compile_correct`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`) for `Assign`,
`LocValue` and `SetGlobal`, resumed at `:798-814`, `:855-874` and `:965-977`.
Bead `flapjack-pxn.18.5.9.22.1`.  The statements take the same form as the
cases in `CompileCorrect/Base.lean`: HOL's goal written out for the
constructor, with no induction hypothesis.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectAssignWitnesses

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

end LoopToWordCompileCorrectAssignWitnesses

/-- Genuine `Assign` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:798-814`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Assign {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (exp : HolLoopExp width) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.assign v exp) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.assign v exp) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.assign v exp) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  split at hEval
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE
  · rename_i w hw
    simp only [Prod.mk.injEq] at hEval
    obtain ⟨rfl, rfl⟩ := hEval
    have hmem : sptMem v ctxt := hAcc v (by simp [accVarsHOL, sptMem_sptInsert])
    have hexp := LoopToWord.compExpPreservesEval s exp w t ctxt ⟨hw, hgd, hState, hLocals⟩
    have hne := LoopToWord.findVarHOL_ne_zero ctxt s.locals t.locals v ⟨hmem, hLocals⟩
    obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState
    refine ⟨WordSemStateFiniteExact.setVar (LoopToWord.findVarHOL ctxt v) w t, none, ?_, ?_, ?_⟩
    · simp only [LoopToWord.compHOL]
      rw [WordSemStateFiniteExact.evaluate, hexp]
    · simpa [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVar] using hffi
    · refine ⟨⟨len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, rfl, rfl⟩
      all_goals first
        | (simp_all [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVar]; done)
        | skip
      · simp only [WordSemStateFiniteExact.setVar]; rw [sptLookup_sptInsert_ne _ _ _ _ (Ne.symm hne)]; exact hRetv
      · exact LoopToWord.localsRelHOLInsert ctxt s.locals t.locals v w ⟨hLocals, hmem⟩

/-- Genuine `LocValue` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:855-874`).  `code_rel`
    carries `l1 ∈ domain s.code` to the target code. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_LocValue {width : Nat} [NeZero width] {C F : Type}
    (r l1 : Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.locValue r l1) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.locValue r l1) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.locValue r l1) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  split at hEval
  · rename_i hsome
    simp only [Prod.mk.injEq] at hEval
    obtain ⟨rfl, rfl⟩ := hEval
    have hmem : sptMem r ctxt := hAcc r (by simp [accVarsHOL, sptMem_sptInsert])
    have hne := LoopToWord.findVarHOL_ne_zero ctxt s.locals t.locals r ⟨hmem, hLocals⟩
    obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState
    have hcodeMem : sptMem l1 t.code := by
      obtain ⟨⟨params, body⟩, hp⟩ := Option.isSome_iff_exists.mp hsome
      have := (hcode l1 params body hp).1
      exact (sptMem_iff_lookup l1 t.code).mpr ⟨_, this⟩
    refine ⟨WordSemStateFiniteExact.setVar (LoopToWord.findVarHOL ctxt r) (.loc l1 0) t, none,
      ?_, ?_, ?_⟩
    · simp only [LoopToWord.compHOL]
      rw [WordSemStateFiniteExact.evaluate, if_pos hcodeMem]
    · simpa [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVar] using hffi
    · refine ⟨⟨len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, rfl, rfl⟩
      all_goals first
        | (simp_all [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVar]; done)
        | skip
      · simp only [WordSemStateFiniteExact.setVar]; rw [sptLookup_sptInsert_ne _ _ _ _ (Ne.symm hne)]; exact hRetv
      · exact LoopToWord.localsRelHOLInsert ctxt s.locals t.locals r _ ⟨hLocals, hmem⟩
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

/-- Genuine `SetGlobal` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:965-977`).  The target
    `Set (Temp dst)` updates the store at `Temp dst`, which keeps `CurrHeap`
    and `HeapLength` and re-establishes `globals_rel`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_SetGlobal {width : Nat} [NeZero width] {C F : Type}
    (dst : BitVec 5) (exp : HolLoopExp width) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.setGlobal dst exp) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.setGlobal dst exp) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.setGlobal dst exp) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  split at hEval
  · rename_i w hw
    simp only [Prod.mk.injEq] at hEval
    obtain ⟨rfl, rfl⟩ := hEval
    have hexp := LoopToWord.compExpPreservesEval s exp w t ctxt ⟨hw, hgd, hState, hLocals⟩
    obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState
    refine ⟨WordSemStateFiniteExact.setStore (.temp dst) w t, none, ?_, ?_, ?_⟩
    · simp only [LoopToWord.compHOL]
      rw [WordSemStateFiniteExact.evaluate]
      simp [hexp]
    · simpa [WordSemStateFiniteExact.setStore, LoopSemStateFiniteExact.setGlobals] using hffi
    · refine ⟨⟨len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, rfl, rfl⟩
      all_goals first
        | (simp_all [WordSemStateFiniteExact.setStore, LoopSemStateFiniteExact.setGlobals,
            FUPDATE_HOL]; done)
        | skip
      · intro n v hv
        simp only [WordSemStateFiniteExact.setStore, LoopSemStateFiniteExact.setGlobals,
          HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq, FUPDATE,
          FUPDATE_HOL] at hv ⊢
        by_cases hn : n = dst
        · subst hn; simp_all
        · have hne : dst ≠ n := Ne.symm hn
          simp only [beq_iff_eq, hne, if_false] at hv
          rw [if_neg (by simp [hn])]
          exact hglob n v hv
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

end Flapjack
