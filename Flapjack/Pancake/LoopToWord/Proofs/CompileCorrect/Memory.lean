import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Arith
import Flapjack.Pancake.Proofs.LoopToWord.CompExpPreservesEval

/-!
# Memory-access cases of `loop_to_word`'s `compile_correct`

These are the exact `loopSem$evaluate_ind` cases of HOL `compile_correct`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`) for `Store`,
`Store32`, `StoreByte`, `Load32` and `LoadByte`, resumed at `:876-964`.
Bead `flapjack-pxn.18.5.9.25`.  The statements take the same form as the
cases in `CompileCorrect/Base.lean`: HOL's goal written out for the
constructor, with no induction hypothesis.  `Store` compiles to wordSem
`Store`.  The other four compile to wordSem `Inst (Mem op r (Addr a 0w))`,
run through `inst`, whose address `a + 0w` is the source
address.
-/

namespace Flapjack

open LoopToWord.CompileCorrect
open LoopToWordCompileCorrectArithSupport

namespace LoopToWordCompileCorrectMemoryWitnesses

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

end LoopToWordCompileCorrectMemoryWitnesses

/-- Flapjack helper (no HOL declaration): the address expression
    `Op Add [Var a; Const 0w]` of a compiled memory instruction evaluates to
    the register's word. -/
private theorem wordExp_addr_zero {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (a : Nat) (w : BitVec width)
    (h : WordSemStateFiniteExact.getVar a t = some (.word w)) :
    WordSemStateFiniteExact.wordExp t (.op .add [.var a, .const (BitVec.ofNat width 0)]) =
      some (.word w) := by
  simp [WordSemStateFiniteExact.wordExp, h, theWords, wordOpHOL, wordOp]

/-- Genuine `Store` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:876-887`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Store {width : Nat} [NeZero width] {C F : Type}
    (exp : HolLoopExp width) (v : Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.store exp v) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ n, sptMem n (accVarsHOL (width := width) (.store exp v) .ln) → sptMem n ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.store exp v) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  have hget : ∀ n w, sptLookup n s.locals = some w →
      WordSemStateFiniteExact.getVar (LoopToWord.findVarHOL ctxt n) t = some w :=
    fun n w h => LoopToWord.localsRelHOLGetVar ctxt s.locals t n w ⟨hLocals, h⟩
  have hState' := hState
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  split at hEval
  · rename_i adr w hadr hw
    split at hEval
    · rename_i st hst
      simp only [Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      have hexp := LoopToWord.compExpPreservesEval s exp _ t ctxt ⟨hadr, hgd, hState, hLocals⟩
      simp only [LoopSemStateFiniteExact.memStore] at hst
      split at hst
      · rename_i hdom
        cases hst
        refine ⟨{ t with memory := fun a => if a = adr then w else t.memory a }, none, ?_, ?_,
          ⟨len, ?_, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩, rfl, hRetv,
          hLocals, rfl, rfl⟩
        · simp only [LoopToWord.compHOL]
          rw [WordSemStateFiniteExact.evaluate, hexp, hget v w hw]
          simp [WordSemStateFiniteExact.memStore, hmd, hdom]
        · exact hffi
        · simp [hm]
      · cases hst
    · simp only [Prod.mk.injEq] at hEval
      exact absurd hEval.1.symm hNE
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

/-- Genuine `Store32` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:889-901`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Store32 {width : Nat} [NeZero width] {C F : Type}
    (a w : Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.store32 a w) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ n, sptMem n (accVarsHOL (width := width) (.store32 a w) .ln) → sptMem n ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.store32 a w) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  have hget : ∀ n w, sptLookup n s.locals = some w →
      WordSemStateFiniteExact.getVar (LoopToWord.findVarHOL ctxt n) t = some w :=
    fun n w h => LoopToWord.localsRelHOLGetVar ctxt s.locals t n w ⟨hLocals, h⟩
  have hState' := hState
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  split at hEval
  · rename_i aw b ha hb
    split at hEval
    · rename_i m hmem
      simp only [Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      refine ⟨{ t with memory := m }, none, ?_, hffi,
        ⟨len, rfl, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩, rfl, hRetv,
        hLocals, rfl, rfl⟩
      simp only [LoopToWord.compHOL]
      rw [WordSemStateFiniteExact.evaluate]
      simp [WordSemStateFiniteExact.inst, wordExp_addr_zero t _ _ (hget a _ ha), hget w _ hb,
        hm, hmd, hbe, hmem]
    · simp only [Prod.mk.injEq] at hEval
      exact absurd hEval.1.symm hNE
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

/-- Genuine `StoreByte` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:903-915`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_StoreByte {width : Nat} [NeZero width] {C F : Type}
    (a w : Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.storeByte a w) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ n, sptMem n (accVarsHOL (width := width) (.storeByte a w) .ln) → sptMem n ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.storeByte a w) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  have hget : ∀ n w, sptLookup n s.locals = some w →
      WordSemStateFiniteExact.getVar (LoopToWord.findVarHOL ctxt n) t = some w :=
    fun n w h => LoopToWord.localsRelHOLGetVar ctxt s.locals t n w ⟨hLocals, h⟩
  have hState' := hState
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  split at hEval
  · rename_i aw b ha hb
    split at hEval
    · rename_i m hmem
      simp only [Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      refine ⟨{ t with memory := m }, none, ?_, hffi,
        ⟨len, rfl, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩, rfl, hRetv,
        hLocals, rfl, rfl⟩
      simp only [LoopToWord.compHOL]
      rw [WordSemStateFiniteExact.evaluate]
      simp [WordSemStateFiniteExact.inst, wordExp_addr_zero t _ _ (hget a _ ha), hget w _ hb,
        hm, hmd, hbe, hmem]
    · simp only [Prod.mk.injEq] at hEval
      exact absurd hEval.1.symm hNE
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

/-- Genuine `Load32` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:917-939`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Load32 {width : Nat} [NeZero width] {C F : Type}
    (a v : Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.load32 a v) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ n, sptMem n (accVarsHOL (width := width) (.load32 a v) .ln) → sptMem n ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.load32 a v) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  have hget : ∀ n w, sptLookup n s.locals = some w →
      WordSemStateFiniteExact.getVar (LoopToWord.findVarHOL ctxt n) t = some w :=
    fun n w h => LoopToWord.localsRelHOLGetVar ctxt s.locals t n w ⟨hLocals, h⟩
  have hState' := hState
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  split at hEval
  · rename_i aw ha
    split at hEval
    · rename_i b hb
      simp only [Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      have hmv : sptMem v ctxt := hAcc v (by simp [accVarsHOL, sptMem_sptInsert])
      obtain ⟨hl, h0⟩ := localsRel_retv_insert ctxt _ _ v (.word (b.setWidth width)) retv
        hLocals hmv hRetv
      refine ⟨WordSemStateFiniteExact.setVar (LoopToWord.findVarHOL ctxt v)
          (.word (b.setWidth width)) t, none, ?_, ?_, stateRel_setVar _ _ _ _ _ _ hState, rfl,
          h0, hl, rfl, rfl⟩
      · simp only [LoopToWord.compHOL]
        rw [WordSemStateFiniteExact.evaluate]
        simp [WordSemStateFiniteExact.inst, wordExp_addr_zero t _ _ (hget a _ ha), hm, hmd, hbe,
          hb]
      · simpa [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVar] using hffi
    · simp only [Prod.mk.injEq] at hEval
      exact absurd hEval.1.symm hNE
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

/-- Genuine `LoadByte` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:941-963`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_LoadByte {width : Nat} [NeZero width] {C F : Type}
    (a v : Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.loadByte a v) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ n, sptMem n (accVarsHOL (width := width) (.loadByte a v) .ln) → sptMem n ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.loadByte a v) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  have hget : ∀ n w, sptLookup n s.locals = some w →
      WordSemStateFiniteExact.getVar (LoopToWord.findVarHOL ctxt n) t = some w :=
    fun n w h => LoopToWord.localsRelHOLGetVar ctxt s.locals t n w ⟨hLocals, h⟩
  have hState' := hState
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  split at hEval
  · rename_i aw ha
    split at hEval
    · rename_i b hb
      simp only [Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      have hmv : sptMem v ctxt := hAcc v (by simp [accVarsHOL, sptMem_sptInsert])
      obtain ⟨hl, h0⟩ := localsRel_retv_insert ctxt _ _ v (.word (b.setWidth width)) retv
        hLocals hmv hRetv
      refine ⟨WordSemStateFiniteExact.setVar (LoopToWord.findVarHOL ctxt v)
          (.word (b.setWidth width)) t, none, ?_, ?_, stateRel_setVar _ _ _ _ _ _ hState, rfl,
          h0, hl, rfl, rfl⟩
      · simp only [LoopToWord.compHOL]
        rw [WordSemStateFiniteExact.evaluate]
        simp [WordSemStateFiniteExact.inst, wordExp_addr_zero t _ _ (hget a _ ha), hm, hmd, hbe,
          hb]
      · simpa [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVar] using hffi
    · simp only [Prod.mk.injEq] at hEval
      exact absurd hEval.1.symm hNE
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

end Flapjack
