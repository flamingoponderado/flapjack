import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEvalShift
import Flapjack.Pancake.Semantics.PanSem.MemLoad32Alt
import Flapjack.Pancake.Semantics.ByteAlignBridge
import Flapjack.Pancake.Semantics.CrepSem.WordAlignment

/-!
# `comp_exp_preserves_eval`: Load32 / LoadByte cases

FLAPJACK-SPECIFIC (not a tagged HOL port, so no `@[hol]` annotation): the
Load32 and LoadByte case pieces of HOL `comp_exp_preserves_eval`
(`cakeml/pancake/proofs/crep_to_loopProofScript.sml:772-781`; the Load32 and
LoadByte cases are at 996-1058), stated over the exact carriers and mirroring
the Shift template `CompExpPreservesEvalShift.lean`.  Each piece takes exactly
the single sub-expression induction hypothesis supplied by HOL's `eval_ind`,
with no extra premises, and the deleted-condition is the same, so the
assembling theorem `flapjack-pxn.18.5.6.33.15.8` carries the
`@[hol ... "comp_exp_preserves_eval"]` tag for the whole statement.

Two case-specific source/target memory-load agreements are proved locally here
(with the existing kernel lemmas `riscvSetByteHOL_eq_holFiniteWordSetByteBitVec`,
`holFiniteWordSetByteBitVec_toNat`, `panGetByteHOL_eq_riscvGetByteHOL`,
`panGetByteHOL_toNat_lt_width` and `RiscV.panRiscVWordOfBytes`); no repository
declaration stated the `wordOfBytesHOL8` / source byte-assembly equality, so
the `loadByte32Aux*` helpers are kept module-local and untagged.
-/

namespace Flapjack

/-- The exact `aligned 2` guard of the target loader is the source loader's
`w2n address MOD 4 = 0` guard. -/
theorem loadByte32AuxRiscvAlignedHOL_two_eq_decide {width : Nat} (a : BitVec width) :
    riscvAlignedHOL 2 a = decide (a.toNat % 4 = 0) := by
  unfold riscvAlignedHOL
  exact (bitVecAligned4_decide_eq_shiftGuard a).symm

/-- The 8-bit target byte widened to `width` is the width-bit image of the
`UInt8` source byte. -/
theorem loadByte32AuxOfNat8_setWidth {width : Nat} (u : UInt8) :
    (BitVec.ofNat 8 u.toNat).setWidth width = BitVec.ofNat width u.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (UInt8.toNat_lt u)]

variable {width : Nat} [NeZero width] {σ : Type}

/-! ## Byte-load and 32-bit-load agreement helpers -/

/-- The target `setByteHOL8` is the source `riscvSetByteHOL` on the byte's
`UInt8` image.  Flapjack-only helper; no HOL declaration states this. -/
theorem loadByte32AuxSetByteHOL8_eq_riscvSetByteHOL {width : Nat} [NeZero width]
    (address value : BitVec width) (byte : BitVec 8) (be : Bool) :
    setByteHOL8 address byte value be =
      riscvSetByteHOL be address value (UInt8.ofNat byte.toNat) := by
  simp only [setByteHOL8, riscvSetByteHOL, byteIndexHOL]
  cases be <;>
    simp only [Bool.false_eq_true, if_false, if_true, UInt8.toNat_ofNat',
      show (2 : Nat) ^ 8 = 256 from rfl, Nat.mod_eq_of_lt byte.isLt, BitVec.ofNat_toNat]

/-- `toNat` of the target `setByteHOL8` at a 32-bit word, via the existing
kernel-checked `holFiniteWordSetByteBitVec_toNat` slice decomposition. -/
theorem loadByte32AuxSetByteHOL8_32_toNat (address value : BitVec 32) (byte : BitVec 8) (be : Bool)
    (h : byteIndexHOL address be + 8 ≤ 32) :
    (setByteHOL8 address byte value be).toNat =
      (value.toNat / 2 ^ (byteIndexHOL address be + 8)) * 2 ^ (byteIndexHOL address be + 8) +
        byte.toNat * 2 ^ (byteIndexHOL address be) +
        value.toNat % 2 ^ (byteIndexHOL address be) := by
  have hb : byteBitIndex address be = byteIndexHOL address be := rfl
  simp only [loadByte32AuxSetByteHOL8_eq_riscvSetByteHOL,
    riscvSetByteHOL_eq_holFiniteWordSetByteBitVec, hb]
  rw [holFiniteWordSetByteBitVec_toNat 32 _ _ _ h]
  simp only [UInt8.toNat_ofNat', show (2 : Nat) ^ 8 = 256 from rfl,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt byte.isLt,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le byte.isLt (by decide : (256 : Nat) ≤ 2 ^ 32))]

/-- Every 32-bit address's `byteIndexHOL` fits its byte lane. -/
theorem loadByte32AuxByteIndexHOL_32_add_eight_le (address : BitVec 32) (be : Bool) :
    byteIndexHOL address be + 8 ≤ 32 := by
  have hm := Nat.mod_lt address.toNat (by decide : 0 < 4)
  simp only [byteIndexHOL, Nat.reduceDiv]
  split <;> omega

/-- `toNat` of the target four-byte `wordOfBytesHOL8` fold. -/
theorem loadByte32AuxWordOfBytesHOL8_four_toNat (be : Bool) (b0 b1 b2 b3 : BitVec 8) :
    (wordOfBytesHOL8 be (0 : BitVec 32) [b0, b1, b2, b3]).toNat =
      (if be then b0.toNat * 2 ^ 24 + b1.toNat * 2 ^ 16 + b2.toNat * 2 ^ 8 + b3.toNat
       else b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24) := by
  cases be
  · simp only [Bool.false_eq_true, if_false, wordOfBytesHOL8]
    rw [show (0 + 1 : BitVec 32) = 1 from by decide,
      show (1 + 1 : BitVec 32) = 2 from by decide,
      show (2 + 1 : BitVec 32) = 3 from by decide]
    rw [loadByte32AuxSetByteHOL8_32_toNat (0 : BitVec 32) _ b0 false
        (loadByte32AuxByteIndexHOL_32_add_eight_le _ _),
      loadByte32AuxSetByteHOL8_32_toNat (1 : BitVec 32) _ b1 false
        (loadByte32AuxByteIndexHOL_32_add_eight_le _ _),
      loadByte32AuxSetByteHOL8_32_toNat (2 : BitVec 32) _ b2 false
        (loadByte32AuxByteIndexHOL_32_add_eight_le _ _),
      loadByte32AuxSetByteHOL8_32_toNat (3 : BitVec 32) _ b3 false
        (loadByte32AuxByteIndexHOL_32_add_eight_le _ _)]
    rw [show byteIndexHOL (0 : BitVec 32) false = 0 from by decide,
      show byteIndexHOL (1 : BitVec 32) false = 8 from by decide,
      show byteIndexHOL (2 : BitVec 32) false = 16 from by decide,
      show byteIndexHOL (3 : BitVec 32) false = 24 from by decide]
    omega
  · simp only [if_true, wordOfBytesHOL8]
    rw [show (0 + 1 : BitVec 32) = 1 from by decide,
      show (1 + 1 : BitVec 32) = 2 from by decide,
      show (2 + 1 : BitVec 32) = 3 from by decide]
    rw [loadByte32AuxSetByteHOL8_32_toNat (0 : BitVec 32) _ b0 true
        (loadByte32AuxByteIndexHOL_32_add_eight_le _ _),
      loadByte32AuxSetByteHOL8_32_toNat (1 : BitVec 32) _ b1 true
        (loadByte32AuxByteIndexHOL_32_add_eight_le _ _),
      loadByte32AuxSetByteHOL8_32_toNat (2 : BitVec 32) _ b2 true
        (loadByte32AuxByteIndexHOL_32_add_eight_le _ _),
      loadByte32AuxSetByteHOL8_32_toNat (3 : BitVec 32) _ b3 true
        (loadByte32AuxByteIndexHOL_32_add_eight_le _ _)]
    rw [show byteIndexHOL (0 : BitVec 32) true = 24 from by decide,
      show byteIndexHOL (1 : BitVec 32) true = 16 from by decide,
      show byteIndexHOL (2 : BitVec 32) true = 8 from by decide,
      show byteIndexHOL (3 : BitVec 32) true = 0 from by decide]
    omega

/-- `toNat` of the source four-byte `panRiscVWordOfBytes` assembly. -/
theorem loadByte32AuxPanRiscVWordOfBytes_four_toNat (be : Bool) (b0 b1 b2 b3 : BitVec 8) :
    (RiscV.panRiscVWordOfBytes (width := 32) be
      [BitVec.ofNat 32 b0.toNat, BitVec.ofNat 32 b1.toNat,
       BitVec.ofNat 32 b2.toNat, BitVec.ofNat 32 b3.toNat]).toNat =
      (if be then b0.toNat * 2 ^ 24 + b1.toNat * 2 ^ 16 + b2.toNat * 2 ^ 8 + b3.toNat
       else b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24) := by
  have hb : ∀ b : BitVec 8, b.toNat < 2 ^ 32 := fun b =>
    Nat.lt_of_lt_of_le b.isLt (by decide : (256 : Nat) ≤ 2 ^ 32)
  cases be
  · simp only [RiscV.panRiscVWordOfBytes, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Bool.false_eq_true, if_false]
    simp only [BitVec.toNat_ofNat]
    have hsum : b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat < 2 ^ 32 := by
      have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt; omega
    rw [Nat.mod_eq_of_lt (hb b0), Nat.mod_eq_of_lt (hb b1), Nat.mod_eq_of_lt (hb b2),
      Nat.mod_eq_of_lt (hb b3), Nat.mod_eq_of_lt hsum]
    omega
  · simp only [RiscV.panRiscVWordOfBytes, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, if_true]
    simp only [BitVec.toNat_ofNat]
    have hsum : b3.toNat + 256 * b2.toNat + 256 ^ 2 * b1.toNat + 256 ^ 3 * b0.toNat < 2 ^ 32 := by
      have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt; omega
    rw [Nat.mod_eq_of_lt (hb b0), Nat.mod_eq_of_lt (hb b1), Nat.mod_eq_of_lt (hb b2),
      Nat.mod_eq_of_lt (hb b3), Nat.mod_eq_of_lt hsum]
    omega

/-- The target `getByteHOL8` is the 8-bit image of the source `panGetByteHOL`. -/
theorem loadByte32AuxGetByteHOL8_eq_ofNat_panGetByteHOL (a v : BitVec width) (be : Bool) :
    getByteHOL8 a v be = BitVec.ofNat 8 (panGetByteHOL a v be).toNat := by
  rw [panGetByteHOL_eq_riscvGetByteHOL]
  simp only [getByteHOL8, riscvGetByteHOL, byteIndexHOL]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_ofNat']
  simp only [show (2 : Nat) ^ 8 = 256 from rfl, Nat.mod_mod]

/-- The width-bit image of a source byte keeps its `toNat`. -/
theorem loadByte32AuxPanGetByteHOL_toNat_ofNat_width (a v : BitVec width) (be : Bool) :
    (BitVec.ofNat width (panGetByteHOL a v be).toNat).toNat =
      (panGetByteHOL a v be).toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (panGetByteHOL_toNat_lt_width a v be)]

/-- The source byte, widened to `word32`, equals the target `getByteHOL8` byte
widened to `word32`. -/
theorem loadByte32AuxPanByte_to32_eq_getByteHOL8_to32 (a v : BitVec width) (be : Bool) :
    BitVec.ofNat 32 (panGetByteHOL a v be).toNat =
      BitVec.ofNat 32 (getByteHOL8 a v be).toNat := by
  rw [loadByte32AuxGetByteHOL8_eq_ofNat_panGetByteHOL, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (UInt8.toNat_lt _)]

/-- The four-byte source and target 32-bit assemblies coincide.  Kernel-only:
    both sides are reduced to the same `Nat` lane sum. -/
theorem loadByte32AuxPanWordOfBytes_eq_wordOfBytesHOL8_four (be : Bool)
    (b0 b1 b2 b3 : BitVec 8) :
    RiscV.panRiscVWordOfBytes (width := 32) be
        [BitVec.ofNat 32 b0.toNat, BitVec.ofNat 32 b1.toNat,
         BitVec.ofNat 32 b2.toNat, BitVec.ofNat 32 b3.toNat] =
      wordOfBytesHOL8 be (0 : BitVec 32) [b0, b1, b2, b3] := by
  apply BitVec.eq_of_toNat_eq
  rw [loadByte32AuxPanRiscVWordOfBytes_four_toNat, loadByte32AuxWordOfBytesHOL8_four_toNat]

/-! ## Memory-load agreement -/

/-- Exact source/target `mem_load_32` agreement over the memory relation. -/
theorem loadByte32AuxLoad32_agree (smem : BitVec width → HolWordLab width)
    (tmem : BitVec width → WordLocW width) (dom : BitVec width → Prop)
    (mdom : BitVec width → Bool) (be : Bool) (aw : BitVec width)
    [DecidablePred dom]
    (hdom : ∀ a, dom a ↔ mdom a = true)
    (hrel : ∀ a, dom a → wlabWlocExact (smem a) = tmem a) :
    memLoad32Exact tmem mdom be aw = panMemLoad32HOL smem dom be aw := by
  have hal : riscvByteAlignHOL aw = panByteAlignHOL aw :=
    riscvByteAlignHOL_eq_panByteAlignHOL aw
  unfold memLoad32Exact panMemLoad32HOL
  rw [loadByte32AuxRiscvAlignedHOL_two_eq_decide, hal]
  dsimp only
  by_cases hg : aw.toNat % 4 = 0
  · rw [if_pos (decide_eq_true hg), if_pos hg]
    by_cases hd : dom (panByteAlignHOL aw)
    · have hm : mdom (panByteAlignHOL aw) = true := (hdom _).mp hd
      generalize hsm : smem (panByteAlignHOL aw) = sv
      cases sv with
      | word val =>
        have ht : tmem (panByteAlignHOL aw) = WordLocW.word val := by
          have h := hrel _ hd
          rw [hsm] at h
          simpa only [wlabWlocExact] using h.symm
        rw [ht]
        dsimp only
        rw [if_pos hd, if_pos hm]
        congr 1
        simp only [List.map_cons, List.map_nil]
        rw [loadByte32AuxPanGetByteHOL_toNat_ofNat_width aw val be,
          loadByte32AuxPanGetByteHOL_toNat_ofNat_width (aw + 1) val be,
          loadByte32AuxPanGetByteHOL_toNat_ofNat_width (aw + 2) val be,
          loadByte32AuxPanGetByteHOL_toNat_ofNat_width (aw + 3) val be,
          loadByte32AuxPanByte_to32_eq_getByteHOL8_to32 aw val be,
          loadByte32AuxPanByte_to32_eq_getByteHOL8_to32 (aw + 1) val be,
          loadByte32AuxPanByte_to32_eq_getByteHOL8_to32 (aw + 2) val be,
          loadByte32AuxPanByte_to32_eq_getByteHOL8_to32 (aw + 3) val be,
          loadByte32AuxPanWordOfBytes_eq_wordOfBytesHOL8_four]
    · have hm : mdom (panByteAlignHOL aw) = false := by
        cases h : mdom (panByteAlignHOL aw) with
        | false => rfl
        | true => exact absurd ((hdom _).mpr h) hd
      rw [if_neg hd]
      cases tmem (panByteAlignHOL aw) <;> simp only [hm, Bool.false_eq_true, if_false]
  · rw [if_neg (by rw [decide_eq_false hg]; decide), if_neg hg]

/-- Exact source/target `mem_load_byte_aux` agreement over the memory relation. -/
theorem loadByte32AuxLoadByte_agree (smem : BitVec width → HolWordLab width)
    (tmem : BitVec width → WordLocW width) (dom : BitVec width → Prop)
    (mdom : BitVec width → Bool) (be : Bool) (aw : BitVec width)
    [DecidablePred dom]
    (hdom : ∀ a, dom a ↔ mdom a = true)
    (hrel : ∀ a, dom a → wlabWlocExact (smem a) = tmem a) :
    memLoadByteAuxExact tmem mdom be aw =
      (panMemLoadByteHOL smem dom be aw).map (fun u => BitVec.ofNat 8 u.toNat) := by
  have hal : riscvByteAlignHOL aw = panByteAlignHOL aw :=
    riscvByteAlignHOL_eq_panByteAlignHOL aw
  unfold memLoadByteAuxExact panMemLoadByteHOL
  rw [hal]
  dsimp only
  by_cases hd : dom (panByteAlignHOL aw)
  · have hm : mdom (panByteAlignHOL aw) = true := (hdom _).mp hd
    generalize hsm : smem (panByteAlignHOL aw) = sv
    cases sv with
    | word val =>
      have ht : tmem (panByteAlignHOL aw) = WordLocW.word val := by
        have h := hrel _ hd
        rw [hsm] at h
        simpa only [wlabWlocExact] using h.symm
      rw [ht]
      dsimp only
      rw [if_pos hd, if_pos hm, loadByte32AuxGetByteHOL8_eq_ofNat_panGetByteHOL]
      rfl
  · have hm : mdom (panByteAlignHOL aw) = false := by
      cases h : mdom (panByteAlignHOL aw) with
      | false => rfl
      | true => exact absurd ((hdom _).mpr h) hd
    rw [if_neg hd]
    cases tmem (panByteAlignHOL aw) <;> simp only [hm, Bool.false_eq_true, if_false] <;> rfl

/-- Inserting a fresh target temporary above `ctxt.vmax` and adding it to the
live set preserves the exact `locals_rel`.  This is the `Load32`/`LoadByte`
"insert into both the live set and the locals" step of the HOL proof, which
`crepToLoopLocalsRelExact_insert_gt_vmax` does not cover because the domain set
grows. -/
theorem loadByte32AuxLocalsRel_insert_dom_gt_vmax (ctxt : CrepToLoopContextExact)
    (live : NumSet) (sLocals : HolFiniteMapExact Nat (HolWordLab width))
    (tLocals : Spt (WordLocW width)) (n : Nat) (w : WordLocW width)
    (h : crepToLoopLocalsRelExact ctxt live sLocals tLocals) (hgt : ctxt.vmax < n) :
    crepToLoopLocalsRelExact ctxt (sptInsert n () live) sLocals (sptInsert n w tLocals) := by
  obtain ⟨hd, hmax, hdom, hmap⟩ := h
  refine ⟨hd, hmax, ?_, ?_⟩
  · intro k hk
    rw [sptMem_sptInsert] at hk
    exact (sptMem_sptInsert k n w tLocals).mpr
      (hk.elim Or.inl (fun hk => Or.inr (hdom k hk)))
  · intro vname value hv
    obtain ⟨m, hvar, hmem, hlk⟩ := hmap vname value hv
    have hmn : m ≠ n := by have := hmax vname m hvar; omega
    exact ⟨m, hvar, (sptMem_sptInsert m n () live).mpr (Or.inr hmem),
      by rw [sptLookup_sptInsert_ne n m w tLocals hmn]; exact hlk⟩

/-- Load32 case piece of HOL `comp_exp_preserves_eval`
(`cakeml/pancake/proofs/crep_to_loopProofScript.sml:996-1058`). -/
theorem comp_exp_preserves_eval_load32 (s : CrepSemHOLState width σ)
    [DecidablePred s.memaddrs] (address : CrepExpHOL width)
    (ihAddress : CrepToLoopCompExpEvalPiece s address) :
    CrepToLoopCompExpEvalPiece s (.load32 address) := by
  intro v t ctxt tmp l p le ntmp nl hEval hState hMem hGlobals hCode hLocals hCompile hTmp
  simp only [evalCrepSemHOLExp] at hEval
  cases ha : evalCrepSemHOLExp s address with
  | none => simp [ha] at hEval
  | some av =>
    rw [ha] at hEval
    cases av with
    | word aw =>
      cases hload : panMemLoad32HOL s.memory s.memaddrs s.be aw with
      | none =>
        change (Option.map (fun value => HolWordLab.word (BitVec.ofNat width value.toNat))
            (panMemLoad32HOL s.memory s.memaddrs s.be aw)) = some v at hEval
        simp only [hload, Option.map_none] at hEval
        simp at hEval
      | some lv =>
        change (Option.map (fun value => HolWordLab.word (BitVec.ofNat width value.toNat))
            (panMemLoad32HOL s.memory s.memaddrs s.be aw)) = some v at hEval
        simp only [hload, Option.map_some, Option.some.injEq] at hEval
        subst hEval
        simp only [compileExpHOLExact] at hCompile
        rcases hA : compileExpHOLExact ctxt tmp l address with ⟨addrCode, addrValue, next, live⟩
        rw [hA] at hCompile
        simp only [Prod.mk.injEq] at hCompile
        obtain ⟨hp, hle, -, hnl⟩ := hCompile
        obtain ⟨ck1, st1, hEval1, hVal1, hState1, hMem1, hGlob1, hCode1, hLoc1⟩ :=
          ihAddress (.word aw) t ctxt tmp l addrCode addrValue next live ha
            hState hMem hGlobals hCode hLocals hA hTmp
        have hVal1' : LoopSemStateFiniteExact.eval st1 addrValue = some (.word aw) := by
          simpa only [wlabWlocExact] using hVal1
        have hnext_ge : tmp ≤ next := by
          have := compileExpHOLExact_tmp_le ctxt tmp l address
          rw [hA] at this
          exact this
        have hvmax : ctxt.vmax < next := Nat.lt_of_lt_of_le hTmp hnext_ge
        have hstate_eq : s.memaddrs = (fun a => st1.mdomain a = true) :=
          ((crepToLoopStateRelExact_intro s st1).mp hState1).1
        have hmemdom : ∀ a, s.memaddrs a ↔ st1.mdomain a = true :=
          fun a => ⟨fun h => by rw [congrFun hstate_eq a] at h; exact h,
            fun h => by rw [congrFun hstate_eq a]; exact h⟩
        have hbe : st1.be = s.be := hState1.2.2.2.1.symm
        have hloadAgree : memLoad32Exact st1.memory st1.mdomain st1.be aw = some lv := by
          rw [hbe, loadByte32AuxLoad32_agree s.memory st1.memory s.memaddrs st1.mdomain s.be aw
            hmemdom hMem1]
          exact hload
        have hAssign : LoopSemStateFiniteExact.evaluate (.assign next addrValue) st1 =
            (none, LoopSemStateFiniteExact.setVar next (.word aw) st1) := by
          simp only [LoopSemStateFiniteExact.evaluate, hVal1']
        have hLoad : LoopSemStateFiniteExact.evaluate (.load32 next next)
            (LoopSemStateFiniteExact.setVar next (.word aw) st1) =
            (none, LoopSemStateFiniteExact.setVar next (.word (lv.setWidth width))
              (LoopSemStateFiniteExact.setVar next (.word aw) st1)) := by
          simp only [LoopSemStateFiniteExact.evaluate, LoopSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
          rw [hloadAgree]
        have hprog : LoopSemStateFiniteExact.evaluate
            (loopNestedSeqHOL [.assign next addrValue, .load32 next next]) st1 =
            (none, LoopSemStateFiniteExact.setVar next (.word (lv.setWidth width))
              (LoopSemStateFiniteExact.setVar next (.word aw) st1)) := by
          change LoopSemStateFiniteExact.evaluate
            (.seq (.assign next addrValue) (.seq (.load32 next next) .skip)) st1 = _
          exact LoopSemStateFiniteExact.evaluate_comb_seq (.assign next addrValue) st1
            (LoopSemStateFiniteExact.setVar next (.word aw) st1) (.seq (.load32 next next) .skip)
            (LoopSemStateFiniteExact.setVar next (.word (lv.setWidth width))
              (LoopSemStateFiniteExact.setVar next (.word aw) st1))
            ⟨hAssign, LoopSemStateFiniteExact.evaluate_comb_seq (.load32 next next)
              (LoopSemStateFiniteExact.setVar next (.word aw) st1)
              (LoopSemStateFiniteExact.setVar next (.word (lv.setWidth width))
                (LoopSemStateFiniteExact.setVar next (.word aw) st1))
              .skip
              (LoopSemStateFiniteExact.setVar next (.word (lv.setWidth width))
                (LoopSemStateFiniteExact.setVar next (.word aw) st1))
              ⟨hLoad, by simp only [LoopSemStateFiniteExact.evaluate]⟩⟩
        have hFull : LoopSemStateFiniteExact.evaluate
            (loopNestedSeqHOL (addrCode ++ [.assign next addrValue, .load32 next next]))
            { t with clock := t.clock + ck1 } =
            (none, LoopSemStateFiniteExact.setVar next (.word (lv.setWidth width))
              (LoopSemStateFiniteExact.setVar next (.word aw) st1)) := by
          rw [LoopSemStateFiniteExact.evaluate_none_nested_seq_append
            (p := addrCode) (s := { t with clock := t.clock + ck1 }) (st := st1)
            (q := [.assign next addrValue, .load32 next next]) hEval1]
          exact hprog
        rw [hp] at hFull
        have hLoc2 : crepToLoopLocalsRelExact ctxt nl s.locals
            (sptInsert next (.word (lv.setWidth width))
              (sptInsert next (.word aw) st1.locals)) := by
          rw [← hnl, sptInsert_insert_shadow]
          exact loadByte32AuxLocalsRel_insert_dom_gt_vmax ctxt live s.locals st1.locals next
            (.word (lv.setWidth width)) hLoc1 hvmax
        refine ⟨ck1, LoopSemStateFiniteExact.setVar next (.word (lv.setWidth width))
            (LoopSemStateFiniteExact.setVar next (.word aw) st1), hFull, ?_,
          hState1, hMem1, hGlob1, hCode1, hLoc2⟩
        · rw [← hle]
          simp only [LoopSemStateFiniteExact.eval, LoopSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same, wlabWlocExact, BitVec.ofNat_toNat]

/-- LoadByte case piece of HOL `comp_exp_preserves_eval`
(`cakeml/pancake/proofs/crep_to_loopProofScript.sml:996-1058`). -/
theorem comp_exp_preserves_eval_loadByte (s : CrepSemHOLState width σ)
    [DecidablePred s.memaddrs] (address : CrepExpHOL width)
    (ihAddress : CrepToLoopCompExpEvalPiece s address) :
    CrepToLoopCompExpEvalPiece s (.loadByte address) := by
  intro v t ctxt tmp l p le ntmp nl hEval hState hMem hGlobals hCode hLocals hCompile hTmp
  simp only [evalCrepSemHOLExp] at hEval
  cases ha : evalCrepSemHOLExp s address with
  | none => simp [ha] at hEval
  | some av =>
    rw [ha] at hEval
    cases av with
    | word aw =>
      cases hload : panMemLoadByteHOL s.memory s.memaddrs s.be aw with
      | none =>
        change (Option.map (fun value => HolWordLab.word (BitVec.ofNat width value.toNat))
            (panMemLoadByteHOL s.memory s.memaddrs s.be aw)) = some v at hEval
        simp only [hload, Option.map_none] at hEval
        simp at hEval
      | some uv =>
        change (Option.map (fun value => HolWordLab.word (BitVec.ofNat width value.toNat))
            (panMemLoadByteHOL s.memory s.memaddrs s.be aw)) = some v at hEval
        simp only [hload, Option.map_some, Option.some.injEq] at hEval
        subst hEval
        simp only [compileExpHOLExact] at hCompile
        rcases hA : compileExpHOLExact ctxt tmp l address with ⟨addrCode, addrValue, next, live⟩
        rw [hA] at hCompile
        simp only [Prod.mk.injEq] at hCompile
        obtain ⟨hp, hle, -, hnl⟩ := hCompile
        obtain ⟨ck1, st1, hEval1, hVal1, hState1, hMem1, hGlob1, hCode1, hLoc1⟩ :=
          ihAddress (.word aw) t ctxt tmp l addrCode addrValue next live ha
            hState hMem hGlobals hCode hLocals hA hTmp
        have hVal1' : LoopSemStateFiniteExact.eval st1 addrValue = some (.word aw) := by
          simpa only [wlabWlocExact] using hVal1
        have hnext_ge : tmp ≤ next := by
          have := compileExpHOLExact_tmp_le ctxt tmp l address
          rw [hA] at this
          exact this
        have hvmax : ctxt.vmax < next := Nat.lt_of_lt_of_le hTmp hnext_ge
        have hstate_eq : s.memaddrs = (fun a => st1.mdomain a = true) :=
          ((crepToLoopStateRelExact_intro s st1).mp hState1).1
        have hmemdom : ∀ a, s.memaddrs a ↔ st1.mdomain a = true :=
          fun a => ⟨fun h => by rw [congrFun hstate_eq a] at h; exact h,
            fun h => by rw [congrFun hstate_eq a]; exact h⟩
        have hbe : st1.be = s.be := hState1.2.2.2.1.symm
        have hloadAgree : memLoadByteAuxExact st1.memory st1.mdomain st1.be aw =
            some (BitVec.ofNat 8 uv.toNat) := by
          rw [hbe, loadByte32AuxLoadByte_agree s.memory st1.memory s.memaddrs st1.mdomain s.be aw
            hmemdom hMem1, hload, Option.map_some]
        have hAssign : LoopSemStateFiniteExact.evaluate (.assign next addrValue) st1 =
            (none, LoopSemStateFiniteExact.setVar next (.word aw) st1) := by
          simp only [LoopSemStateFiniteExact.evaluate, hVal1']
        have hLoad : LoopSemStateFiniteExact.evaluate (.loadByte next next)
            (LoopSemStateFiniteExact.setVar next (.word aw) st1) =
            (none, LoopSemStateFiniteExact.setVar next
              (.word ((BitVec.ofNat 8 uv.toNat).setWidth width))
              (LoopSemStateFiniteExact.setVar next (.word aw) st1)) := by
          simp only [LoopSemStateFiniteExact.evaluate, LoopSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
          rw [hloadAgree]
        have hprog : LoopSemStateFiniteExact.evaluate
            (loopNestedSeqHOL [.assign next addrValue, .loadByte next next]) st1 =
            (none, LoopSemStateFiniteExact.setVar next
              (.word ((BitVec.ofNat 8 uv.toNat).setWidth width))
              (LoopSemStateFiniteExact.setVar next (.word aw) st1)) := by
          change LoopSemStateFiniteExact.evaluate
            (.seq (.assign next addrValue) (.seq (.loadByte next next) .skip)) st1 = _
          exact LoopSemStateFiniteExact.evaluate_comb_seq (.assign next addrValue) st1
            (LoopSemStateFiniteExact.setVar next (.word aw) st1) (.seq (.loadByte next next) .skip)
            (LoopSemStateFiniteExact.setVar next (.word ((BitVec.ofNat 8 uv.toNat).setWidth width))
              (LoopSemStateFiniteExact.setVar next (.word aw) st1))
            ⟨hAssign, LoopSemStateFiniteExact.evaluate_comb_seq (.loadByte next next)
              (LoopSemStateFiniteExact.setVar next (.word aw) st1)
              (LoopSemStateFiniteExact.setVar next (.word ((BitVec.ofNat 8 uv.toNat).setWidth width))
                (LoopSemStateFiniteExact.setVar next (.word aw) st1))
              .skip
              (LoopSemStateFiniteExact.setVar next (.word ((BitVec.ofNat 8 uv.toNat).setWidth width))
                (LoopSemStateFiniteExact.setVar next (.word aw) st1))
              ⟨hLoad, by simp only [LoopSemStateFiniteExact.evaluate]⟩⟩
        have hFull : LoopSemStateFiniteExact.evaluate
            (loopNestedSeqHOL (addrCode ++ [.assign next addrValue, .loadByte next next]))
            { t with clock := t.clock + ck1 } =
            (none, LoopSemStateFiniteExact.setVar next
              (.word ((BitVec.ofNat 8 uv.toNat).setWidth width))
              (LoopSemStateFiniteExact.setVar next (.word aw) st1)) := by
          rw [LoopSemStateFiniteExact.evaluate_none_nested_seq_append
            (p := addrCode) (s := { t with clock := t.clock + ck1 }) (st := st1)
            (q := [.assign next addrValue, .loadByte next next]) hEval1]
          exact hprog
        rw [hp] at hFull
        have hLoc2 : crepToLoopLocalsRelExact ctxt nl s.locals
            (sptInsert next (.word ((BitVec.ofNat 8 uv.toNat).setWidth width))
              (sptInsert next (.word aw) st1.locals)) := by
          rw [← hnl, sptInsert_insert_shadow]
          exact loadByte32AuxLocalsRel_insert_dom_gt_vmax ctxt live s.locals st1.locals next
            (.word ((BitVec.ofNat 8 uv.toNat).setWidth width)) hLoc1 hvmax
        refine ⟨ck1, LoopSemStateFiniteExact.setVar next
            (.word ((BitVec.ofNat 8 uv.toNat).setWidth width))
            (LoopSemStateFiniteExact.setVar next (.word aw) st1), hFull, ?_,
          hState1, hMem1, hGlob1, hCode1, hLoc2⟩
        · rw [← hle]
          simp only [LoopSemStateFiniteExact.eval, LoopSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same, wlabWlocExact, loadByte32AuxOfNat8_setWidth]

end Flapjack

