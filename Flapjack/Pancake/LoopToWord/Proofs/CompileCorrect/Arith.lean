import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelUpdates
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups
import Flapjack.Pancake.Proofs.LoopToWord.FindVar

/-!
# `Arith` and `Primitive` cases of `loop_to_word`'s `compile_correct`

These are the exact `loopSem$evaluate_ind` cases of HOL `compile_correct`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`) for `Arith` and
`Primitive`, resumed at `:1431-1447` and `:816-853`.  Bead
`flapjack-pxn.18.5.9.22.2`.  The statements take the same form as the cases
in `CompileCorrect/Base.lean`: HOL's goal written out for the constructor,
with no induction hypothesis.  The target runs through the tagged wordSem
`inst` (`inst_def`).
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectArithWitnesses

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

end LoopToWordCompileCorrectArithWitnesses

namespace LoopToWordCompileCorrectArithSupport

/-- Flapjack helper (no HOL declaration): `state_rel` survives a local
    variable update on both sides, as HOL's `state_rel_def` does not mention
    locals. -/
theorem stateRel_setVar {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (n m : Nat) (v w : WordLocW width) (h : loopToWordStateRelHOLExact s t) :
    loopToWordStateRelHOLExact (LoopSemStateFiniteExact.setVar n v s)
      (WordSemStateFiniteExact.setVar m w t) := by
  obtain ⟨len, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨len, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- Flapjack helper (no HOL declaration): a mapped update of a variable in
    the context domain keeps `locals_rel` and the value of register 0.  It
    combines the tagged `locals_rel_insert` and `find_var_neq_0`. -/
theorem localsRel_retv_insert {width : Nat} [NeZero width] (ctxt : Spt Nat)
    (sl tl : Spt (WordLocW width)) (n : Nat) (v retv : WordLocW width)
    (hrel : LoopToWord.localsRelHOL ctxt sl tl) (hmem : sptMem n ctxt)
    (h0 : sptLookup 0 tl = some retv) :
    LoopToWord.localsRelHOL ctxt (sptInsert n v sl)
        (sptInsert (LoopToWord.findVarHOL ctxt n) v tl) ∧
      sptLookup 0 (sptInsert (LoopToWord.findVarHOL ctxt n) v tl) = some retv := by
  have hne := LoopToWord.findVarHOL_ne_zero ctxt sl tl n ⟨hmem, hrel⟩
  exact ⟨LoopToWord.localsRelHOLInsert ctxt sl tl n v ⟨hrel, hmem⟩,
    by rw [sptLookup_sptInsert_ne _ _ _ _ (Ne.symm hne)]; exact h0⟩

/-- Flapjack helper (no HOL declaration): a successful loopSem `get_vars`
    returns one value per name. -/
theorem loopGetVars_some {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) :
    ∀ (ns : List Nat) (ws : List (WordLocW width)),
      LoopSemStateFiniteExact.getVars ns s = some ws →
        ws.length = ns.length ∧ ∀ i (h : i < ns.length),
          sptLookup (ns.get ⟨i, h⟩) s.locals = ws[i]?
  | [], ws, h => by
      simp [LoopSemStateFiniteExact.getVars] at h; subst h; simp
  | n :: ns, ws, h => by
      simp only [LoopSemStateFiniteExact.getVars] at h
      cases hn : sptLookup n s.locals with
      | none => simp [hn] at h
      | some v =>
        cases hns : LoopSemStateFiniteExact.getVars ns s with
        | none => simp [hn, hns] at h
        | some vs =>
          simp [hn, hns] at h
          subst h
          obtain ⟨hl, hi⟩ := loopGetVars_some s ns vs hns
          refine ⟨by simp [hl], ?_⟩
          intro i hi'
          cases i with
          | zero => simpa using hn
          | succ i => simpa using hi i (by simpa using hi')

theorem list_length_eq_three {α : Type} (l : List α) (h : l.length = 3) :
    ∃ a b c, l = [a, b, c] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, rfl⟩

theorem list_length_eq_two {α : Type} (l : List α) (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp at h
  exact ⟨a, b, rfl⟩

end LoopToWordCompileCorrectArithSupport

open LoopToWordCompileCorrectArithSupport

/-- Genuine `Arith` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:1431-1447`).  Each of
    `LDiv`, `LLongMul` and `LLongDiv` compiles to the matching wordSem `Inst
    (Arith ...)` over `find_var`-renamed registers.  The operands are read
    through `locals_rel`, and the destinations are updated in the same order
    on both sides. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Arith {width : Nat} [NeZero width] {C F : Type}
    (arith : LoopArith) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.arith arith) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.arith arith) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.arith arith) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, -, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  split at hEval
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE
  · rename_i s' hs'
    simp only [Prod.mk.injEq] at hEval
    obtain ⟨rfl, rfl⟩ := hEval
    have hget : ∀ n w, sptLookup n s.locals = some w →
        WordSemStateFiniteExact.getVar (LoopToWord.findVarHOL ctxt n) t = some w :=
      fun n w h => LoopToWord.localsRelHOLGetVar ctxt s.locals t n w ⟨hLocals, h⟩
    have hffi := hState.choose_spec.2.2.2.2.2.1
    cases arith with
    | div r1 r2 r3 =>
      simp only [LoopSemStateFiniteExact.loopArith] at hs'
      split at hs'
      · rename_i q w2 hq hw2
        split at hs'
        · rename_i hq0
          cases hs'
          have hmem : sptMem r1 ctxt := hAcc r1 (by simp [accVarsHOL, sptMem_sptInsert])
          obtain ⟨hl, h0⟩ := localsRel_retv_insert ctxt _ _ r1 (.word (w2.sdiv q)) retv hLocals hmem hRetv
          refine ⟨WordSemStateFiniteExact.setVar (LoopToWord.findVarHOL ctxt r1) (.word (w2.sdiv q)) t,
            none, ?_, ?_, stateRel_setVar _ _ _ _ _ _ hState, rfl, h0, hl, rfl, rfl⟩
          · simp only [LoopToWord.compHOL]
            rw [WordSemStateFiniteExact.evaluate]
            simp [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars, hget _ _ hq,
              hget _ _ hw2]
            rw [if_neg (by intro h; exact hq0 (by simpa using h))]
          · simpa [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVar] using hffi
        · cases hs'
      · cases hs'
    | longMul r1 r2 r3 r4 =>
      simp only [LoopSemStateFiniteExact.loopArith] at hs'
      split at hs'
      · rename_i w3 w4 h3 h4
        cases hs'
        have hm1 : sptMem r1 ctxt := hAcc r1 (by simp [accVarsHOL, sptMem_sptInsert])
        have hm2 : sptMem r2 ctxt := hAcc r2 (by simp [accVarsHOL, sptMem_sptInsert])
        obtain ⟨hl1, h01⟩ := localsRel_retv_insert ctxt _ _ r1
          (.word (BitVec.ofNat width (w3.toNat * w4.toNat / 2 ^ width))) retv hLocals hm1 hRetv
        obtain ⟨hl2, h02⟩ := localsRel_retv_insert ctxt _ _ r2
          (.word (BitVec.ofNat width (w3.toNat * w4.toNat))) retv hl1 hm2 h01
        refine ⟨_, none, ?_, ?_, stateRel_setVar _ _ _ _ _ _ (stateRel_setVar _ _ _ _ _ _ hState),
          rfl, h02, hl2, rfl, rfl⟩
        · simp only [LoopToWord.compHOL]
          rw [WordSemStateFiniteExact.evaluate]
          simp [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars, hget _ _ h3,
            hget _ _ h4]
        · simpa [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVar] using hffi
      · cases hs'
    | longDiv r1 r2 r3 r4 r5 =>
      simp only [LoopSemStateFiniteExact.loopArith] at hs'
      split at hs'
      · rename_i w3 w4 w5 h3 h4 h5
        split at hs'
        · rename_i hc
          cases hs'
          have hm1 : sptMem r1 ctxt := hAcc r1 (by simp [accVarsHOL, sptMem_sptInsert])
          have hm2 : sptMem r2 ctxt := hAcc r2 (by simp [accVarsHOL, sptMem_sptInsert])
          obtain ⟨hl2, h02⟩ := localsRel_retv_insert ctxt _ _ r2
            (.word (BitVec.ofNat width ((w3.toNat * 2 ^ width + w4.toNat) % w5.toNat)))
            retv hLocals hm2 hRetv
          obtain ⟨hl1, h01⟩ := localsRel_retv_insert ctxt _ _ r1
            (.word (BitVec.ofNat width ((w3.toNat * 2 ^ width + w4.toNat) / w5.toNat)))
            retv hl2 hm1 h02
          refine ⟨_, none, ?_, ?_,
            stateRel_setVar _ _ _ _ _ _ (stateRel_setVar _ _ _ _ _ _ hState),
            rfl, h01, hl1, rfl, rfl⟩
          · simp only [LoopToWord.compHOL]
            rw [WordSemStateFiniteExact.evaluate]
            simp [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars, hget _ _ h3,
              hget _ _ h4, hget _ _ h5, hc]
          · simpa [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVar] using hffi
        · cases hs'
      · cases hs'

/-- Genuine `Primitive` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:816-853`).  The only
    primitive is `AddCarry`.  It compiles to four wordSem steps through the
    odd scratch registers 1 and 3, which `find_var` never produces
    (`find_var_neq_odd`).  So the scratch writes are unmapped updates
    (`locals_rel_insert_unmapped`), and the two destination writes are mapped
    updates (`locals_rel_insert`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Primitive {width : Nat} [NeZero width] {C F : Type}
    (lhss : List Nat) (pop : PrimOp) (rhss : List Nat) (s : LoopSemStateFiniteExact width F) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.primitive lhss pop rhss) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.primitive lhss pop rhss) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.primitive lhss pop rhss) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, -, -, hAcc⟩
  simp only [LoopSemStateFiniteExact.evaluate] at hEval
  have hffi := hState.choose_spec.2.2.2.2.2.1
  have hodd : ∀ k, k % 2 ≠ 0 → ∀ n, LoopToWord.findVarHOL ctxt n ≠ k := fun k hk n =>
    LoopToWord.findVarHOL_ne_odd ctxt n k ⟨hLocals.2.1, hk⟩
  have h1 := hodd 1 (by decide)
  have h3 := hodd 3 (by decide)
  have hget : ∀ n w, sptLookup n s.locals = some w →
      WordSemStateFiniteExact.getVar (LoopToWord.findVarHOL ctxt n) t = some w :=
    fun n w h => LoopToWord.localsRelHOLGetVar ctxt s.locals t n w ⟨hLocals, h⟩
  split at hEval
  · rename_i ws hws
    split at hEval
    · rename_i resWs hres
      split at hEval
      · rename_i hlen
        simp only [Prod.mk.injEq] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        unfold LoopSemStateFiniteExact.loopPrimop at hres
        split at hres
        · rename_i lw rw cw
          cases hres
          obtain ⟨hrl, hri⟩ := loopGetVars_some s rhss _ hws
          obtain ⟨a, b, c, rfl⟩ := list_length_eq_three rhss (by simpa using hrl.symm)
          obtain ⟨x, y, rfl⟩ := list_length_eq_two lhss (by simpa using hlen)
          have ha := hri 0 (by simp)
          have hb := hri 1 (by simp)
          have hc := hri 2 (by simp)
          simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ,
            List.getElem?_cons_zero, List.getElem?_cons_succ] at ha hb hc
          have hseq := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
            (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
          have hasg := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
            (F := F)).2.2.2.2.2.1
          have hins := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
            (F := F)).2.2.2.2.1
          refine ⟨WordSemStateFiniteExact.setVar (LoopToWord.findVarHOL ctxt x)
              (.word (wordAddCarryHOL lw rw cw).1)
              (WordSemStateFiniteExact.setVar (LoopToWord.findVarHOL ctxt y)
                (.word (wordAddCarryHOL lw rw cw).2)
                (WordSemStateFiniteExact.setVar 1 (.word (wordAddCarryHOL lw rw cw).2)
                  (WordSemStateFiniteExact.setVar 3 (.word (wordAddCarryHOL lw rw cw).1)
                    (WordSemStateFiniteExact.setVar 1 (.word cw) t)))), none, ?_, ?_⟩
          · have hga := hget a _ ha
            have hgb := hget b _ hb
            have hgc := hget c _ hc
            simp only [WordSemStateFiniteExact.getVar] at hga hgb hgc
            simp only [LoopToWord.compHOL, hseq, hasg, hins]
            simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
              WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
              WordSemStateFiniteExact.setVar, hga, hgb, hgc, sptLookup_sptInsert_same,
              sptLookup_sptInsert_ne, h1, fun n => (h3 n).symm]
          have hmx : sptMem x ctxt := hAcc x (by simp [accVarsHOL, sptListInsert, sptMem_sptInsert])
          have hmy : sptMem y ctxt := hAcc y (by simp [accVarsHOL, sptListInsert, sptMem_sptInsert])
          have hx0 := LoopToWord.findVarHOL_ne_zero ctxt s.locals t.locals x ⟨hmx, hLocals⟩
          have hy0 := LoopToWord.findVarHOL_ne_zero ctxt s.locals t.locals y ⟨hmy, hLocals⟩
          have hU := LoopToWord.localsRelHOLInsertUnmapped ctxt s.locals _ 1
            (.word (wordAddCarryHOL lw rw cw).2)
            ⟨LoopToWord.localsRelHOLInsertUnmapped ctxt s.locals _ 3
              (.word (wordAddCarryHOL lw rw cw).1)
              ⟨LoopToWord.localsRelHOLInsertUnmapped ctxt s.locals t.locals 1 (.word cw)
                ⟨hLocals, fun n _ => h1 n⟩, fun n _ => h3 n⟩, fun n _ => h1 n⟩
          have hL := LoopToWord.localsRelHOLInsert ctxt _ _ x (.word (wordAddCarryHOL lw rw cw).1)
            ⟨LoopToWord.localsRelHOLInsert ctxt _ _ y (.word (wordAddCarryHOL lw rw cw).2)
              ⟨hU, hmy⟩, hmx⟩
          obtain ⟨len, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hState
          refine ⟨?_, ⟨len, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩, rfl, ?_, ?_, rfl, rfl⟩
          · simpa [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVars] using hffi
          · simp only [WordSemStateFiniteExact.setVar]
            rw [sptLookup_sptInsert_ne _ _ _ _ (Ne.symm hx0), sptLookup_sptInsert_ne _ _ _ _ (Ne.symm hy0),
              sptLookup_sptInsert_ne _ _ _ _ (by decide), sptLookup_sptInsert_ne _ _ _ _ (by decide),
              sptLookup_sptInsert_ne _ _ _ _ (by decide)]
            exact hRetv
          · simpa [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVars,
              LoopSemStateFiniteExact.sptAlistInsert, wordAddCarryHOL] using hL
        · cases hres
      · simp only [Prod.mk.injEq] at hEval
        exact absurd hEval.1.symm hNE
    · simp only [Prod.mk.injEq] at hEval
      exact absurd hEval.1.symm hNE
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE

end Flapjack
