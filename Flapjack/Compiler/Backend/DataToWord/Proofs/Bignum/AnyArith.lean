module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyHeader
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Assemble
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Headers
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.Arith
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.CodeRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.DivCodeAssum
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.MustTerminate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.Replicate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutLocals
public import Flapjack.Compiler.Backend.WordBignum.Proofs.EvaluateMcIop

@[expose] public section

/-! The general bignum arithmetic stub (`AnyArith_code`). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace AnyArithWitness
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AnyArithWitness

open Classical in
/-- The general arithmetic stub computes the integer operation selected by
`op_index` on two related integers, or reports that the heap is too small.
HOL's test `q = SOME NotEnoughSpace` uses classical decidability.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "AnyArith_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem anyArith_thm {width : Nat} [NeZero width] {C F : Type} :
    ∀ (op_index : Nat) (i j v : Int) (t : WordSemStateFiniteExact width C F)
      (s : DataSem.State C F) (r2 r1 : Nat) (locs : List (Nat × Nat)) (l2 l1 : Nat) (c : Config),
      stateRel c l1 l2 s t none locs ∧
        DataSem.getVars [0, 1, 2] s.locals =
          some [.number i, .number j, .number (op_index : Int)] ∧
        t.clock = wordSemMustTerminateLimit width - 2 ∧ t.termdep ≠ 0 ∧
        sptLookup 6 t.locals = some (.word (BitVec.ofNat width (4 * op_index) : BitVec width)) ∧
        intOp op_index i j = some v →
      ∃ (q : Option (WordSemResult width)) (r : WordSemStateFiniteExact width C F) (new_c : Nat),
        WordSemStateFiniteExact.evaluate (anyArithCode c) t = (q, r) ∧
        if q = some .notEnoughSpace then
          r.ffi = t.ffi ∧
            (c.gcKind ≠ .none ∧ DataSem.noThunksInRefs s.refs →
              let il := DataSem.bignumSize s.limits.arch64Bit i
              let jl := DataSem.bignumSize s.limits.arch64Bit j
              il + jl ≤ 2 ^ c.lenSize →
                s.limits.heapLimit <
                  il + jl + DataSem.sizeOfHeap (cutLocals (sptFromList [(), (), ()]) s))
        else
          ∃ rv : WordLocW width, q = some (.result (.loc l1 l2) [rv]) ∧
            stateRel c r1 r2
              { s with locals := .ln, localsSize := some 0, clock := new_c, space := 0,
                       stackMax := none } r (some [(.number v, rv)]) locs := by
  intro op_index i j v t s r2 r1 locs l2 l1 c ⟨rel, gv, clk, td, h6, hop⟩
  obtain ⟨hi, hj, _⟩ := AnyArith.getVars_three gv
  rw [AnyArith.anyArithCode_eq]
  rw [AnyArith.evaluate_prefix rel hi hj, WordSemStateFiniteExact.BignumClauses.evaluate_seq]
  generalize hrun : WordSemStateFiniteExact.evaluate (allocVar c (2 ^ c.lenSize)
    (sptListInsert [0, 1, 2] .ln)) ((t.setVar 1 (.word (AnyArith.sizeWord width i j))).setStore
      (.temp 29) (.word (AnyArith.sizeWord width i j))) = qr
  obtain ⟨q, r⟩ := qr
  have A := AnyArith.alloc_step rel gv hrun
  by_cases hq : q = some .notEnoughSpace
  · subst hq
    refine ⟨some .notEnoughSpace, r, 0, rfl, ?_⟩
    rw [if_pos rfl]
    exact A.1 rfl
  obtain ⟨qn, rel1, t29, code, nlt⟩ := A.2 hq
  subst qn
  dsimp only
  have good : goodDimindex width := rel.2.2.2.2.2.2.1
  have termd : r.termdep = t.termdep := (WordSemStateFiniteExact.evaluate_clock _ _ _ _ hrun).2
  set il := (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.length with hil
  set jl := (Misc.Multiword.i2mw j : Bool × List (BitVec width)).2.length with hjl
  set L0 : Spt DataSem.Value := sptFromList [.number i, .number j, .number (op_index : Int)]
    with hL0
  have hi0 : DataSem.getVar 0 L0 = some (.number i) := by
    simp [L0, DataSem.getVar, sptLookupFromList]
  have hj0 : DataSem.getVar 1 L0 = some (.number j) := by
    simp [L0, DataSem.getVar, sptLookupFromList]
  have h20 : DataSem.getVar 2 L0 = some (.number (op_index : Int)) := by
    simp [L0, DataSem.getVar, sptLookupFromList]
  obtain ⟨a2, a3, a2', a3', tmp, tmp', eH, rel9, fi, fj⟩ :=
    AnyArith.headers_step (s0 := { s with locals := L0, space := il + jl + 2 }) rel1 hi0 hj0
      (AnyArith.setupCode (.seq (.call (some ([1], (.ls (), .ln), .skip, anyArithLocation, 3))
        (some bignumLocation) [] none) (AnyArith.postCode c)))
  rw [eH]
  set s9 := AnyArith.headerState r i j a2 a3 a2' a3' tmp tmp' with hs9
  set n := il + jl + 1 with hn
  have rel9' : stateRel c l1 l2 { s with locals := L0, space := n + 1 } s9 none locs := rel9
  have mem9 := rel9'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap, limit, a, sp, sp1, gens, ha, hb, k, curr, other, x0, ow, xs, hims, wml, lim, spLe,
    hheap, ha_len, spk, limNZ, lxs, hcurr, hother, hnext, H⟩ := AnyArith.heap_split mem9 rfl
  obtain ⟨_, _, _, _, _, hopc⟩ := AnyArith.intOp_getIop hop
  have hsz : AnyArith.sizeWord width i j = BitVec.ofNat width (4 * n) := by
    simp only [AnyArith.sizeWord, hn, show 4 * (il + jl + 1) = 4 * il + 4 * jl + 4 by omega,
      BitVec.ofNat_add]
    rw [show (BitVec.ofNat width 4) = 4 from rfl]
    ac_rfl
  have st9 : ∀ q : BitVec 5, q ≠ BitVec.ofNat 5 11 → q ≠ BitVec.ofNat 5 30 → q ≠ BitVec.ofNat 5 1 →
      q ≠ BitVec.ofNat 5 0 → q ≠ BitVec.ofNat 5 31 → q ≠ BitVec.ofNat 5 12 →
      s9.store.lookup (.temp q) = r.store.lookup (.temp q) := by
    intro q n11 n30 n1 n0 n31 n12
    simp [s9, AnyArith.headerState, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.setVar, FUPDATE_HOL, n11, n30, n1, n0, n31, n12]
  have h11 : s9.store.lookup (.temp 11) = some (.word a3') := by
    simp [s9, AnyArith.headerState, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.setVar, FUPDATE_HOL]
  have h12 : s9.store.lookup (.temp 12) = some (.word a3) := by
    simp [s9, AnyArith.headerState, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.setVar, FUPDATE_HOL]
  have h29 : s9.store.lookup (.temp 29) = some (.word (BitVec.ofNat width (4 * n))) := by
    rw [st9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t29, hsz]
  obtain ⟨wv, hw⟩ := stateRel_getVar c l1 l2 _ s9 none locs 2 _ rel9' h20
  have m2 := memoryRel_lookup c s9.be (holThe s.tstamps) s.refs (n + 1) s9.store s9.memory
    s9.mdomain L0 s9.locals ([(theGlobal s.global, holFapply s9.store .globals)] ++
      flatStack s.stack s9.stack) 2 (.number (op_index : Int)) wv
    ⟨by simpa [List.append_assoc] using mem9, h20, hw⟩
  have smOp : smallInt width (op_index : Int) := by
    unfold smallInt
    have : 64 ≤ 2 ^ width / 8 := by rcases good with h | h <;> rw [h] <;> norm_num
    simp only [Int.ofNat_eq_natCast]
    rcases hopc with h | h | h | h | h <;> subst h <;> constructor <;> omega
  have wvE := memoryRel_numberImp c _ _ _ _ _ _ _ _ _ _ ⟨good, smOp, m2⟩
  have h6' : sptLookup 6 s9.locals = some (.word (BitVec.ofNat width (4 * op_index))) := by
    have e : (smallnum (op_index : Int) : BitVec width) = BitVec.ofNat width (4 * op_index) := by
      unfold smallnum
      rw [if_neg (by omega)]
      congr 1
    rw [← e, ← wvE]; exact hw
  have lsz := AnyArith.lenSize_bound rel
  have w4 : 64 < 2 ^ width ∧ 32 ≤ width := by
    rcases good with h | h <;> rw [h] <;> norm_num
  have hsh : wordShiftHOL .lsr (BitVec.ofNat width (4 * op_index)) (BitVec.ofNat width 2).toNat =
      some (BitVec.ofNat width (4 * op_index) >>> (BitVec.ofNat width 2).toNat) := by
    unfold wordShiftHOL
    rw [if_neg]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have h0 : sptLookup 0 s9.locals = some (.loc l1 l2) := rel9'.2.2.2.2.2.2.2.2.2.2.1 rfl
  have hcode9 := (lookupRefByteLocation c l1 l2 _ s9 locs rel9').2.2.2.1
  have pl : 2 ^ c.lenSize * 16 ≤ 2 ^ width := by
    rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb4 : 4 * n < 2 ^ width := by omega
  have clk9 : s9.clock = wordSemMustTerminateLimit width - 2 := by
    rw [show s9.clock = r.clock from rfl, rel1.2.1]
    show s.clock = _
    rw [← rel.2.1, clk]
  have mtl := mustTerminateLimit_sub_2 width good
  have hc : n < s9.clock := by rw [clk9]; omega
  obtain ⟨m2, ms, eS, H6⟩ := AnyArith.setup_step h11 h12 h29 hother hnext h6' hsh h0 hcode9 lxs hb4 hc
    H _
  rw [eS]
  obtain ⟨hmw, hdivj, hlt, heq, hdec, _⟩ := AnyArith.intOp_getIop hop
  obtain ⟨_, sizeLt⟩ := AnyArith.sizeWord_toNat rel hi hj
  obtain ⟨xx1, xx2, xx3, xx4, xx5, hcomp⟩ : ∃ a b c' d e, WordBignum.compile bignumLocation 2 1
      (bignumLocation + 1, []) (WordBignum.mcIopCode width) = (a, b, c', d, e) := by
    generalize WordBignum.compile bignumLocation 2 1 (bignumLocation + 1, [])
      (WordBignum.mcIopCode width) = res
    obtain ⟨a, b, c', d, e⟩ := res
    exact ⟨a, b, c', d, e, rfl⟩
  have hcodeB : sptLookup bignumLocation s9.code = some (1, .seq xx1 (.return 0 [0])) := by
    refine rel9'.2.2.2.2.1.2.1 (bignumLocation, 1, .seq xx1 (.return 0 [0])) ?_
    simp only [stubs, List.mem_append]
    right
    simp only [WordBignum.generatedBignumStubs, hcomp, List.mem_cons]
    left; trivial
  have crel := impBignumCodeRel xx1 xx2 xx3 xx4 xx5 c l1 l2 _ s9 locs ⟨hcomp, rel9'⟩
  have dca := divCodeAssum_thm c l1 l2 _ s9 locs rel9'
  have td9 : s9.termdep ≠ 0 := by
    rw [show s9.termdep = r.termdep from rfl, termd]; exact td
  have wml' : wordMlInv (heap, s9.be, a, sp, sp1, gens) limit (holThe s.tstamps) c s.refs
      (joinEnv L0 (sptToAList (sptInter s9.locals (adjustSet L0))) ++
        ([(theGlobal s.global, holFapply s9.store .globals)] ++ flatStack s.stack s9.stack)) := by
    simpa [List.append_assoc] using wml
  have fi9 := AnyArith.HeaderFacts.toHeaderState (i := i) (j := j) (b2 := a2) (b3 := a3)
    (b2' := a2') (b3' := a3') (tmp := tmp) (tmp' := tmp') (by decide) fi
  have fj9 := AnyArith.HeaderFacts.toHeaderState (i := i) (j := j) (b2 := a2) (b3 := a3)
    (b2' := a2') (b3' := a3') (tmp := tmp) (tmp' := tmp') (by decide) fj
  have csi := AnyArith.operand_side (sd := s) (oth := other) fi9 hi0 wml' good hims.1 hcurr hheap
    (P := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength ha)) hnext
  have csj := AnyArith.operand_side (sd := s) (oth := other) fj9 hj0 wml' good hims.1 hcurr hheap
    (P := other) hother
  obtain ⟨R1, arr1⟩ := AnyArith.operand_arr H6 csi
  have H6' := H6
  rw [show ∀ (W A B FR : ((BitVec width × WordLocW width) → Prop) → Prop),
      SetSep.star W (SetSep.star A (SetSep.star B FR)) =
        SetSep.star W (SetSep.star B (SetSep.star A FR)) by intros; ac_rfl] at H6'
  obtain ⟨R2, arr2⟩ := AnyArith.operand_arr H6' csj
  set u := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength ha) with hu
  set w3 := BitVec.ofNat width (4 * op_index) >>> (BitVec.ofNat width 2).toNat with hw3
  set t9 := AnyArith.setupState s9 u w3 m2 n (.loc l1 l2) ms with ht9
  have stT : ∀ q : BitVec 5, q ≠ BitVec.ofNat 5 29 → q ≠ BitVec.ofNat 5 3 →
      t9.store.lookup (.temp q) = s9.store.lookup (.temp q) := by
    intro q n29 n3
    simp [t9, AnyArith.setupState, FUPDATE_HOL, n29, n3]
  have st0 : t9.store.lookup (.temp 0) =
      some (.word (Misc.Multiword.mcHeader (Misc.Multiword.i2mw i : Bool × List (BitVec width)))) := by
    rw [stT _ (by decide) (by decide)]
    simp [s9, AnyArith.headerState, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.setVar, FUPDATE_HOL]
  have st1 : t9.store.lookup (.temp 1) =
      some (.word (Misc.Multiword.mcHeader (Misc.Multiword.i2mw j : Bool × List (BitVec width)))) := by
    rw [stT _ (by decide) (by decide)]
    simp [s9, AnyArith.headerState, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.setVar, FUPDATE_HOL]
  have st3 : t9.store.lookup (.temp 3) =
      some (.word (Misc.Multiword.intOpRep (getIop op_index))) := by
    rw [← AnyArith.opWord good hopc]
    simp [t9, AnyArith.setupState, FUPDATE_HOL, w3]
  have sIn1 : t9.store.lookup WordBignum.tempIn1 = some (.word a2) := by
    rw [show WordBignum.tempIn1 = .temp 31 from rfl, stT _ (by decide) (by decide)]
    simp [s9, AnyArith.headerState, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.setVar, FUPDATE_HOL]
  have sIn2 : t9.store.lookup WordBignum.tempIn2 = some (.word a2') := by
    rw [show WordBignum.tempIn2 = .temp 30 from rfl, stT _ (by decide) (by decide)]
    simp [s9, AnyArith.headerState, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.setVar, FUPDATE_HOL]
  have sOut : t9.store.lookup WordBignum.tempOut = some (.word (u + wordSemBytesInWord)) := by
    simp [t9, AnyArith.setupState, FUPDATE_HOL, WordBignum.tempOut]
  obtain ⟨kk, hk⟩ := mustTerminateLimit_eq width good
  have wlt : width < 2 ^ width := Nat.lt_two_pow_self
  have hmax : Misc.Multiword.mcDivMax (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2
      (Misc.Multiword.i2mw j : Bool × List (BitVec width)).2 (List.replicate n 0) + 2 * n + 2 ≤
      t9.clock - 1 := by
    have tc : t9.clock = s9.clock - n - 1 := rfl
    rw [tc, clk9]
    simp only [Misc.Multiword.mcDivMax, List.length_replicate]
    have m1 : il * (2 ^ width + 2 * jl + 4) ≤ 2 ^ width * (2 ^ width + 2 ^ width + 4) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e1 : 2 ^ width * (2 ^ width + 2 ^ width + 4) = 2 * (2 ^ width * 2 ^ width) + 4 * 2 ^ width := by
      ring
    have e2 : 10 * 2 ^ width * 2 ^ width = 10 * (2 ^ width * 2 ^ width) := by ring
    rw [e2] at hk
    simp only [← hil, ← hjl] at sizeLt ⊢
    omega
  obtain ⟨t2, zs1, l2', eC, hlen2, hstack2, rel2, code2, hret⟩ := AnyArith.iop_call_step (t9 := t9)
    (l1 := l1) (l2 := l2) rfl hcomp hcodeB crel dca td9 st0 st1 st3 sIn1 sIn2 sOut arr1 arr2 H6
    hdivj hmax (by omega) (by omega) hlt heq hdec good (AnyArith.postCode c)
  rw [eC]
  obtain ⟨_, ⟨A1, A2, A3, _, _, _, _, h3o, _, _, outR⟩, regs2, _, _, _, ggc, ghand, _, gcode, gbe,
    gffi, gcomp, goracle, gcb, gdb, gsl, gss, gtout, gnt⟩ := rel2
  set R0 := AnyArith.afterCallState t9 (WordSemStateFiniteExact.flushState false t2) (.loc l1 l2)
  have t9nt : ∀ key, (∀ q, key ≠ WordStore.temp q) → t9.store.lookup key = s9.store.lookup key := by
    intro key h
    simp [t9, AnyArith.setupState, FUPDATE_HOL, h (BitVec.ofNat 5 29), h (BitVec.ofNat 5 3)]
  have hstoreR : ∀ key, (∀ q, key ≠ WordStore.temp q) → R0.store.lookup key = s9.store.lookup key := by
    intro key h
    rw [show R0.store = t2.store from rfl, gnt key h]
    exact t9nt key h
  have a3e : A3 = u + wordSemBytesInWord := by
    rw [gtout] at h3o
    have : (AnyArith.bignumCallState t9 (.loc l1 l2)).store.lookup WordBignum.tempOut =
        some (.word (u + wordSemBytesInWord)) := sOut
    rw [this] at h3o
    cases h3o; rfl
  subst a3e
  have outE : (AnyArith.iopFinal i j (getIop op_index) (List.replicate n 0) zs1 (t9.clock - 1)
      l2').arrays .out = (Misc.Multiword.i2mw (Misc.Multiword.mwIntOp (getIop op_index) i j) :
        Bool × List (BitVec width)).2 ++ zs1 := by
    simp [AnyArith.iopFinal, WordBignum.CorrSupport.deleteVars_arrays, WordBignum.clockWrite,
      WordBignum.CorrSupport.regWrite_arrays, WordBignum.arrayWrite]
  rw [outE, hmw] at outR
  have r10 := regs2 10 (Misc.Multiword.mcHeader
      (Misc.Multiword.i2mw (Misc.Multiword.mwIntOp (getIop op_index) i j) : Bool × List (BitVec width)))
    (by simp [AnyArith.iopFinal, WordBignum.CorrSupport.deleteVars_lookup, WordBignum.clockWrite,
      WordBignum.regWrite, WordBignum.arrayWrite, FUPDATE_HOL])
  rw [hmw] at r10
  have P : AnyArith.PostHyps c l1 l2 s L0 s9 R0 locs n heap ha hb limit a sp sp1 k gens curr other
      (.word a3) (.word a3') v zs1 :=
    { rel9 := rel9', hims := hims, wml := wml, lim := lim, spLe := spLe, hheap := hheap,
      ha_len := ha_len, limNZ := limNZ, hys := by simpa [hmw] using hlen2, hn := nlt,
      hstore := hstoreR, hmem := outR, hcurr := hcurr, hother := hother, hnext := hnext,
      hffi := gffi.symm, hhandler := ghand.symm, hgc := ggc.symm, hcode := gcode.symm,
      hcomp := gcomp.symm, horacle := goracle.symm, hcb := gcb.symm, hdb := gdb.symm,
      hbe := gbe.symm, hss := gss.symm, hsl := gsl.symm, hstack := rfl,
      hmax := AnyArith.stackMax_after (t9 := t9) (F2 := WordSemStateFiniteExact.flushState false t2)
        hret, h10 := r10.2,
      h0 := by simp [R0, AnyArith.afterCallState, sptLookup_sptInsert_ne]; rfl }
  obtain ⟨q, rr, new_c, ePost, rv, hq', relF⟩ := AnyArith.post_step P r1 r2 good (by omega)
  refine ⟨q, rr, new_c, ePost, ?_⟩
  rw [if_neg (by rw [hq']; simp)]
  exact ⟨rv, hq', relF⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
