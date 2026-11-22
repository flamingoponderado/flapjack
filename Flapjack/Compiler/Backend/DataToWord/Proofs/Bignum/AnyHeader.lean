module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.NumSize
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.WordBits
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.DerefByte
public import Flapjack.FiniteMap.MapKeys
public import Flapjack.Misc.Multiword.Mc.Basics

@[expose] public section

/-! Header computation for a bignum-arithmetic operand (`AnyHeader`). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace AnyHeaderWitness
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AnyHeaderWitness

private theorem setStore_comm {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (k1 k2 : WordStoreHOL) (v1 v2 : WordLocW width)
    (ne : k1 ≠ k2) :
    (s.setStore k1 v1).setStore k2 v2 = (s.setStore k2 v2).setStore k1 v1 := by
  simp only [WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.mk.injEq, and_true,
    true_and]
  apply HolFiniteMapExact.ext_lookup
  intro k
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  by_cases h1 : k = k1 <;> by_cases h2 : k = k2 <;> simp_all

private theorem setVar_setStore {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (n : Nat) (k : WordStoreHOL) (v w : WordLocW width) :
    (s.setStore k w).setVar n v = (s.setVar n v).setStore k w := rfl

private theorem seqSet {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : BitVec 5) (e : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (read : t.wordExp e = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.set (.temp k) e) p) t =
      WordSemStateFiniteExact.evaluate p (t.setStore (.temp k) v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setStore]

private theorem seqAssign' {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : Nat) (e : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (read : t.wordExp e = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign k e) p) t =
      WordSemStateFiniteExact.evaluate p (t.setVar k v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

private theorem evalSet {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : BitVec 5) (e : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (read : t.wordExp e = some v) :
    WordSemStateFiniteExact.evaluate (.set (.temp k) e) t = (none, t.setStore (.temp k) v) := by
  simp [WordSemStateFiniteExact.evaluate, read]

private theorem evalAssign {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : Nat) (e : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (read : t.wordExp e = some v) :
    WordSemStateFiniteExact.evaluate (.assign k e) t = (none, t.setVar k v) := by
  simp [WordSemStateFiniteExact.evaluate, read]

private theorem andOp_eq' {width : Nat} (x y : BitVec width) : AndOp.and x y = x &&& y := rfl

private theorem setStore_perm321 {width : Nat} [NeZero width] {C F : Type}
    (S : WordSemStateFiniteExact width C F) (k1 k2 k3 : BitVec 5) (v1 v2 v3 : WordLocW width)
    (d12 : k1 ≠ k2) (d13 : k1 ≠ k3) (d23 : k2 ≠ k3) :
    ((S.setStore (.temp k1) v1).setStore (.temp k2) v2).setStore (.temp k3) v3 =
      ((S.setStore (.temp k3) v3).setStore (.temp k2) v2).setStore (.temp k1) v1 := by
  rw [setStore_comm (S.setStore (.temp k1) v1) (.temp k2) (.temp k3) v2 v3 (by simpa using d23),
    setStore_comm S (.temp k1) (.temp k3) v1 v3 (by simpa using d13),
    setStore_comm (S.setStore (.temp k3) v3) (.temp k1) (.temp k2) v1 v2 (by simpa using d12)]

/-- Small-integer facts for the immediate branch: Flapjack arithmetic infrastructure. -/
private theorem smallnum_signedLess {width : Nat} [NeZero width] (good : goodDimindex width)
    (i : Int) (small : smallInt width i) :
    Compiler.Encoders.Asm.holAsmSignedLess (smallnum i : BitVec width) 0 = decide (i < 0) := by
  have b := smallnum_signedBounds good i small
  rw [smallnum_i2w]
  rcases good with h | h <;> subst h <;>
    simp only [Compiler.Encoders.Asm.holAsmSignedLess, BitVec.toNat_ofInt] <;>
    by_cases neg : i < 0 <;> simp [neg] <;> omega

private theorem smallnum_neg_shift {width : Nat} [NeZero width] (good : goodDimindex width)
    (i : Int) (small : smallInt width i) (neg : i < 0) :
    -((smallnum i : BitVec width).sshiftRight 2) = BitVec.ofNat width i.natAbs := by
  have b := smallnum_signedBounds good i small
  have pos : 0 < width := by rcases good with h | h <;> omega
  have sh : (smallnum i : BitVec width).sshiftRight 2 = BitVec.ofInt width i := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sshiftRight, smallnum_i2w, BitVec.toInt_ofInt, BitVec.toInt_ofInt]
    rcases good with h | h <;> subst h <;> norm_num at b <;>
      simp only [Int.bmod, Int.shiftRight_eq_div_pow] <;> split_ifs <;> omega
  rw [sh, ← BitVec.ofInt_neg, show -i = ((i.natAbs : Nat) : Int) by omega, BitVec.ofInt_natCast]

/-- The header code stores the multiword header and the payload location of a
related integer. HOL's `i2mw i` in the zero case has an independent word
dimension (`w2`). The evaluator inherits the real-model assumption in
`docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "AnyHeader_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem anyHeader_thm {width : Nat} {w2 : Nat} [NeZero width] [NeZero w2] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (i : Int) (a : Bool) :
    ∀ (t1 t2 t3 : BitVec 5) (r : Nat),
      stateRel c l1 l2 s t none locs ∧ DataSem.getVar r s.locals = some (.number i) ∧
        [t1, t2, t3].Nodup →
      ∃ (a2 a3 : BitVec width) (temp : WordLocW width),
        WordSemStateFiniteExact.evaluate (anyHeader c (adjustVar r) a t1 t2 t3) t =
          (none, ((((t.setVar 7 temp).setStore (.temp t3) (.word a3)).setStore (.temp t2)
            (.word a2)).setStore (.temp t1)
            (.word (Misc.Multiword.mcHeader (Misc.Multiword.i2mw i : Bool × List (BitVec width)))))) ∧
        (i = 0 → smallInt width 0 ∧ (Misc.Multiword.i2mw i : Bool × List (BitVec w2)) = (false, []) ∧
          a2 = 0 ∧ a3 = 0) ∧
        (smallInt width i ∧ i ≠ 0 →
          (Misc.Multiword.i2mw i : Bool × List (BitVec width)) = (decide (i < 0), [a3]) ∧
          t.store.lookup (if a then .otherHeap else .nextFree) = some (.word a2)) ∧
        (¬ smallInt width i → ∃ w x : BitVec width,
          WordSemStateFiniteExact.getVar (adjustVar r) t = some (.word w) ∧
          getRealAddr c t.store w = some x ∧ a2 = x + wordSemBytesInWord) := by
  intro t1 t2 t3 r ⟨rel, found, nodup⟩
  have d12 : t1 ≠ t2 := by intro e; simp [e] at nodup
  have d13 : t1 ≠ t3 := by intro e; simp [e] at nodup
  have d23 : t2 ≠ t3 := by intro e; simp [e] at nodup
  obtain ⟨wv, hw⟩ := stateRel_getVar c l1 l2 s t none locs r _ rel found
  have good : goodDimindex width := rel.2.2.2.2.2.2.1
  have shiftLt : shiftLength c < width := rel.2.2.2.2.2.2.2.1
  have mem := rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have m2 := memoryRel_lookup c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain
    s.locals t.locals ([(theGlobal s.global, holFapply t.store .globals)] ++ flatStack s.stack t.stack)
    r (.number i) wv ⟨by simpa [List.append_assoc] using mem, found, hw⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, _, _, lenNe, lenLt, _, _, curr, other, _, _, _, hother, hnext, _⟩, _⟩ :=
    id m2
  obtain ⟨w4, rfl, bit⟩ := memoryRel_anyNumberImp c t.be (holThe s.tstamps) s.refs s.space t.store
    t.memory t.mdomain i _ _ ⟨good, m2⟩
  have wpos : 32 ≤ width := by rcases good with h | h <;> omega
  have hr : WordSemStateFiniteExact.getVar (adjustVar r) t = some (.word w4) := hw
  have test0 := memoryRel_numberConstTest c t.be (holThe s.tstamps) s.refs s.space t.store t.memory
    t.mdomain i 0 w4 _ ⟨m2, good⟩
  have small0 : smallInt width 0 := by
    have : 0 < 2 ^ width / 8 := Nat.div_pos (by
      calc 8 = 2 ^ 3 := rfl
        _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)) (by decide)
    unfold smallInt
    rw [Int.ofNat_eq_natCast]
    constructor <;> omega
  rw [if_pos small0] at test0
  have sn0 : (smallnum 0 : BitVec width) = 0 := by simp [smallnum]
  rw [sn0] at test0
  have hr7 (v : WordLocW width) : sptLookup (adjustVar r) (t.setVar 7 v).locals = some (.word w4) := by
    simp only [WordSemStateFiniteExact.setVar]
    rw [sptLookup_sptInsert_ne _ _ _ _ (by simp [adjustVar]; omega)]; exact hw
  by_cases hz : w4 = 0
  · subst hz
    have i0 : i = 0 := test0.1 rfl
    subst i0
    have H0 : Misc.Multiword.mcHeader (Misc.Multiword.i2mw 0 : Bool × List (BitVec width)) = 0 := by
      simp [Misc.Multiword.i2mw, Misc.Multiword.n2mw, Misc.Multiword.mcHeader]
    refine ⟨0, 0, .word 0, ?_, ?_, ?_, ?_⟩
    · rw [anyHeader, WordSemStateFiniteExact.evaluate]
      simp only [WordSemStateFiniteExact.getVarImm, hr, wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.ofNat_eq_ofNat, beq_self_eq_true]
      simp only [wordListSeq.eq_3, wordListSeq.eq_2]
      rw [seqAssign' t 7 _ (.word 0) _ (by simp [WordSemStateFiniteExact.wordExp])]
      rw [seqSet _ t1 _ (.word 0) _ (by
        simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, hr7])]
      rw [seqSet _ t2 _ (.word 0) _ (by
        simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setStore, hr7])]
      rw [evalSet _ t3 _ (.word 0) (by
        simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setStore, hr7])]
      rw [H0, setStore_perm321 _ t1 t2 t3 _ _ _ d12 d13 d23]
      rfl
    · intro _; exact ⟨small0, by simp [Misc.Multiword.i2mw, Misc.Multiword.n2mw], rfl, rfl⟩
    · intro h; exact absurd rfl h.2
    · intro h; exact absurd small0 h
  have ine : i ≠ 0 := fun e => hz (test0.2 e).symm
  have hz' : (w4 == 0#width) = false := by simpa using hz
  by_cases hb : w4.getLsbD 0 = true
  · have nsmall : ¬ smallInt width i := bit.1 hb
    obtain ⟨_, w', x, A, hv, h1, hreal, hdom, hmem, _, _, _, hsign, _, _, _, _, _, _, hdec⟩ :=
      memoryRel_number_bignumImp_alt c t.be (holThe s.tstamps) s.refs s.space t.store t.memory
        t.mdomain i (.word w4) _ ⟨m2, nsmall, good⟩
    cases hv
    have ra := getRealAddr_lemma c (adjustVar r) t w4 A ⟨shiftLt, good, hr, hreal⟩
    have h1' : (AndOp.and w4 1#width != 0#width) = true := by
      simp only [bne_iff_ne, ne_eq]; exact h1
    refine ⟨A + wordSemBytesInWord, 0, .word A, ?_, ?_, ?_, ?_⟩
    · rw [anyHeader, WordSemStateFiniteExact.evaluate]
      simp only [WordSemStateFiniteExact.getVarImm, hr, wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.ofNat_eq_ofNat, hz']
      rw [WordSemStateFiniteExact.evaluate]
      simp only [WordSemStateFiniteExact.getVarImm, hr, wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.ofNat_eq_ofNat, h1']
      simp only [wordListSeq.eq_3, wordListSeq.eq_2]
      rw [seqAssign' t 7 _ (.word A) _ ra]
      have g7 : WordSemStateFiniteExact.getVar 7 (t.setVar 7 (.word A)) = some (.word A) := by
        simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
          sptLookup_sptInsert_same]
      rw [seqSet _ t2 _ (.word (A + wordSemBytesInWord)) _ (by
        simp [WordSemStateFiniteExact.wordExp, g7, theWords, wordOpHOL, wordOp,
          wordSemBytesInWord])]
      have shAmt : (BitVec.ofNat width (width - c.lenSize)).toNat = width - c.lenSize :=
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) Nat.lt_two_pow_self)
      have small4 (n : Nat) (hn : n ≤ 4) : (BitVec.ofNat width n).toNat = n :=
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hn (Nat.lt_of_lt_of_le (by decide : 4 < 2 ^ 32)
          (Nat.pow_le_pow_right (by decide) wpos)))
      have nsh : ¬ (¬ width - c.lenSize = 0 ∧ width ≤ width - c.lenSize) := by omega
      have w1 : ¬ width ≤ 1 := by omega
      have w4' : ¬ width ≤ 4 := by omega
      have hd : x >>> (width - c.lenSize) =
          BitVec.ofNat width (Misc.Multiword.n2mw i.natAbs : List (BitVec width)).length := hdec
      have sgn : (1 &&& x >>> (4 : Nat)) = if decide (i < 0) then 1 else 0 := by
        rw [getSignWord_lemma x good]
        have : x.getLsbD 4 = decide (i < 0) := by
          have := hsign; simp only [show 4 ≤ width - 1 by omega, true_and] at this
          by_cases h : i < 0 <;> simp_all
        rw [this]
      have hdr : Misc.Multiword.mcHeader (Misc.Multiword.i2mw i : Bool × List (BitVec width)) =
          (x >>> (width - c.lenSize)) <<< (1 : Nat) + (1 &&& x >>> (4 : Nat)) := by
        rw [hd, sgn]
        simp only [Misc.Multiword.mcHeader, Misc.Multiword.i2mw]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one]
        rw [Nat.mod_mul_mod]
      rw [seqSet _ t1 _ (.word (Misc.Multiword.mcHeader
          (Misc.Multiword.i2mw i : Bool × List (BitVec width)))) _ (by
        rw [hdr]
        simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad,
          WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same,
          WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar, hdom, hmem, shiftN,
          wordShiftHOL, shAmt, small4, nsh, w1, w4', theWords, wordOpHOL, wordOp, andOp_eq']
        )]
      rw [evalSet _ t3 _ (.word 0) (by simp [WordSemStateFiniteExact.wordExp])]
      rw [setStore_comm _ (.temp t1) (.temp t3) _ _ (by simpa using d13),
        setStore_comm _ (.temp t2) (.temp t3) _ _ (by simpa using d23)]
      rfl
    · intro h; exact absurd h ine
    · intro h; exact absurd h.1 nsmall
    · intro _; exact ⟨w4, A, hr, hreal, rfl⟩
  · have small : smallInt width i := by
      by_contra ns; exact hb (bit.2 ns)
    have hw4 := memoryRel_numberImp c t.be (holThe s.tstamps) s.refs s.space t.store t.memory
      t.mdomain i (.word w4) _ ⟨good, small, m2⟩
    cases hw4
    have hb' : (smallnum i : BitVec width).getLsbD 0 = false := by simpa using hb
    have h1' : (AndOp.and (smallnum i : BitVec width) 1#width != 0#width) = false := by
      have := (word_index_test (n := 0) (w := (smallnum i : BitVec width)) (by omega)).not
      simp only [hb', Bool.false_eq_true, not_not, Nat.pow_zero] at this
      simp only [bne_eq_false_iff_eq]
      exact this.mp (by simp)
    have lt : i.natAbs < 2 ^ width := by
      obtain ⟨lo, hi⟩ := small
      rw [Int.ofNat_eq_natCast] at lo hi
      have : 2 ^ width / 8 ≤ 2 ^ width := Nat.div_le_self _ _
      omega
    have digits : (Misc.Multiword.n2mw i.natAbs : List (BitVec width)) =
        [BitVec.ofNat width i.natAbs] := by
      rw [Misc.Multiword.n2mw, if_neg (by omega), Nat.div_eq_of_lt lt, Misc.Multiword.n2mw,
        Nat.mod_eq_of_lt lt]
      simp
    obtain ⟨hv, hheap⟩ : ∃ hv : BitVec width,
        t.store.lookup (if a then .otherHeap else .nextFree) = some (.word hv) := by
      cases a
      · exact ⟨_, hnext⟩
      · exact ⟨_, hother⟩
    have nl := smallnum_signedLess good i small
    have two_mod : 2 % 2 ^ width = 2 :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 2 < 2 ^ 32)
        (Nat.pow_le_pow_right (by decide) wpos))
    have wle2 : ¬ width ≤ 2 := by omega
    have hne1 : ∀ k : BitVec 5, (if a then WordStore.otherHeap else WordStore.nextFree : WordStoreHOL) ≠
        WordStore.temp k := by
      intro k; cases a <;> simp
    have heapExp : ∀ (S : WordSemStateFiniteExact width C F), S.store.lookup
        (if a then .otherHeap else .nextFree) = some (.word hv) →
        S.wordExp (.lookup (if a then .otherHeap else .nextFree)) = some (.word hv) := by
      intro S h; simpa [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore] using h
    refine ⟨hv, BitVec.ofNat width i.natAbs, .word 0, ?_, ?_, ?_, ?_⟩
    · have hrS : ∀ (S : WordSemStateFiniteExact width C F), S.locals = t.locals →
          S.getVar (adjustVar r) = some (.word (smallnum i)) := by
        intro S h; simp only [WordSemStateFiniteExact.getVar, h]; exact hw
      rw [anyHeader, WordSemStateFiniteExact.evaluate]
      simp only [WordSemStateFiniteExact.getVarImm, hr, wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.ofNat_eq_ofNat, hz']
      rw [WordSemStateFiniteExact.evaluate]
      simp only [WordSemStateFiniteExact.getVarImm, hr, wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.ofNat_eq_ofNat, h1']
      rw [WordSemStateFiniteExact.evaluate]
      have nl' : Compiler.Encoders.Asm.holAsmSignedLess (smallnum i : BitVec width) 0#width =
          decide (i < 0) := nl
      simp only [WordSemStateFiniteExact.getVarImm, hr, wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, nl']
      have hrT := hrS t rfl
      by_cases neg : i < 0
      · have H3 : Misc.Multiword.mcHeader (Misc.Multiword.i2mw i : Bool × List (BitVec width)) =
            3 := by
          simp [Misc.Multiword.mcHeader, Misc.Multiword.i2mw, digits, neg]
          rw [BitVec.ofNat_add_ofNat]
        simp only [neg, decide_true, Bool.not_true]
        simp only [wordListSeq.eq_3, wordListSeq.eq_2]
        rw [seqSet t t1 _ (.word 3) _ (by simp [WordSemStateFiniteExact.wordExp])]
        rw [seqSet _ t2 _ (.word hv) _ (heapExp _ (by
          simpa [WordSemStateFiniteExact.setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
            hne1] using hheap))]
        rw [seqSet _ t3 _ (.word (BitVec.ofNat width i.natAbs)) _ (by
          have hwl : sptLookup (adjustVar r) t.locals = some (.word (smallnum i)) := hw
          simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
            WordSemStateFiniteExact.setStore, hwl, shiftN, wordShiftHOL, theWords, wordOpHOL, wordOp,
            two_mod, wle2]
          exact smallnum_neg_shift good i small neg)]
        rw [evalAssign _ 7 _ (.word 0) (by simp [WordSemStateFiniteExact.wordExp])]
        rw [H3, ← setVar_setStore, ← setVar_setStore, ← setVar_setStore,
          setStore_perm321 _ t1 t2 t3 _ _ _ d12 d13 d23]
        rfl
      · have H2 : Misc.Multiword.mcHeader (Misc.Multiword.i2mw i : Bool × List (BitVec width)) =
            2 := by
          simp [Misc.Multiword.mcHeader, Misc.Multiword.i2mw, digits, neg]
        have nn : 0 ≤ i := by omega
        simp only [neg, decide_false, Bool.not_false]
        simp only [wordListSeq.eq_3, wordListSeq.eq_2]
        rw [seqSet t t1 _ (.word 2) _ (by simp [WordSemStateFiniteExact.wordExp])]
        rw [seqSet _ t2 _ (.word hv) _ (heapExp _ (by
          simpa [WordSemStateFiniteExact.setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
            hne1] using hheap))]
        rw [seqSet _ t3 _ (.word (BitVec.ofNat width i.natAbs)) _ (by
          have hwl : sptLookup (adjustVar r) t.locals = some (.word (smallnum i)) := hw
          have sh := Assign.smallnum_nonneg_shift i good small nn
          have nat : (i.toNat : Nat) = i.natAbs := by omega
          rw [nat] at sh
          simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
            WordSemStateFiniteExact.setStore, hwl, shiftN, wordShiftHOL, two_mod, wle2]
          simpa [BitVec.ushiftRight_eq', two_mod] using sh)]
        rw [evalAssign _ 7 _ (.word 0) (by simp [WordSemStateFiniteExact.wordExp])]
        rw [H2, ← setVar_setStore, ← setVar_setStore, ← setVar_setStore,
          setStore_perm321 _ t1 t2 t3 _ _ _ d12 d13 d23]
        rfl
    · intro h; exact absurd h ine
    · intro _
      exact ⟨by simp [Misc.Multiword.i2mw, digits], hheap⟩
    · intro h; exact absurd small h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
