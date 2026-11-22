module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.RefByte
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SetByteSort
public import Flapjack.Compiler.Backend.LabToTarget.InstMem
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Misc.GetByteSetByte

@[expose] public section

/-! Correctness of the generated `WriteLastBytes` byte-store sequence. -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.HolByte

namespace WriteLastBytesWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WriteLastBytesWitness

/-- Distinct in-range numeric lane offsets `c` and `c + 1 + j` select distinct
byte lanes. -/
private theorem byteIndex_lane_ne {width : Nat} [NeZero width] (good : goodDimindex width)
    (c : BitVec width) (j : Nat) (be : Bool) (fit : c.toNat + j + 2 ≤ width / 8) :
    byteIndex c be ≠ byteIndex (c + 1#width + BitVec.ofNat width j) be := by
  rcases good with rfl | rfl <;>
  · have hj : (c + 1#_ + BitVec.ofNat _ j).toNat = c.toNat + 1 + j := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      norm_num at fit ⊢
      omega
    simp only [byteIndex, hj]
    norm_num at fit ⊢
    split <;> omega

/-- The innermost write of `last_bytes` can be moved outermost: Flapjack
infrastructure for `evaluate_WriteLastBytes`, which performs the writes in the
opposite order. -/
theorem lastBytes_succ {width : Nat} [NeZero width] (good : goodDimindex width)
    (b : BitVec 8) (w : BitVec width) (be : Bool) :
    ∀ (i : Nat) (c : BitVec width), c.toNat + i + 1 ≤ width / 8 →
      lastBytes (i + 1) b c w be = setByte (c + BitVec.ofNat width i) b (lastBytes i b c w be) be := by
  intro i
  induction i with
  | zero =>
    intro c _
    rw [lastBytes, if_neg (by omega)]
    simp [lastBytes]
  | succ j ih =>
    intro c fit
    have lt : c.toNat + 1 < 2 ^ width := by
      have : width / 8 ≤ 2 ^ width :=
        le_trans (Nat.div_le_self _ _) (Nat.lt_two_pow_self).le
      omega
    have c1 : (c + 1#width).toNat = c.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      rcases good with rfl | rfl <;> norm_num at lt fit ⊢ <;> omega
    rw [lastBytes, if_neg (by omega), Nat.add_sub_cancel, ih (c + 1#width) (by omega),
      setByte_commute _ _ _ _ _ _ (byteIndex_lane_ne good c j be (by omega))]
    conv => rhs; rw [lastBytes, if_neg (by omega), Nat.add_sub_cancel]
    congr 1
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm 1 j]

/-- The memory of `s` with the word at `a` replaced by `v`. -/
private abbrev withWordAt {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (a v : BitVec width) :
    WordSemStateFiniteExact width C F :=
  { s with memory := fun x => if x = a then .word v else s.memory x }

/-- One `WriteLastByte_aux` step: Flapjack infrastructure for
`evaluate_WriteLastBytes`. -/
private theorem evaluate_writeLastByteAux {width : Nat} [NeZero width] {C F : Type}
    (good : goodDimindex width) (s : WordSemStateFiniteExact width C F) (av bv nv : Nat)
    (a b n : BitVec width)
    (ha : WordSemStateFiniteExact.getVar av s = some (.word a))
    (hb : WordSemStateFiniteExact.getVar bv s = some (.word b))
    (hn : WordSemStateFiniteExact.getVar nv s = some (.word n))
    (hdom : s.mdomain a = true) (off : BitVec width) (v : BitVec width)
    (p : WordLangProgHOL (BitVec width)) (halign : holByteAlign (a + off) = a) :
    WordSemStateFiniteExact.evaluate (writeLastByteAux off av bv nv p) (withWordAt s a v) =
      if n = off then (none, withWordAt s a v)
      else WordSemStateFiniteExact.evaluate p (withWordAt s a (setByte (a + off) (b.setWidth 8) v s.be)) := by
  have align' : riscvByteAlignHOL (a + off) = a := by
    rw [LabToTarget.riscvByteAlignHOL_eq good, halign]
  have ha' : WordSemStateFiniteExact.getVar av (withWordAt s a v) = some (.word a) := ha
  have hb' : WordSemStateFiniteExact.getVar bv (withWordAt s a v) = some (.word b) := hb
  have hn' : WordSemStateFiniteExact.getVar nv (withWordAt s a v) = some (.word n) := hn
  by_cases e : n = off
  · subst e
    simp [writeLastByteAux, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, hn']
  · have ne : (n == off) = false := by simpa using e
    simp [writeLastByteAux, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, hn', ne,
      theWords, wordOpHOL, wordOp,
      WordSemStateFiniteExact.inst, WordSemStateFiniteExact.wordExp, ha', hb',
      memStoreByteAuxExact, align', hdom, LabToTarget.setByteHOL8_eq,
      WordSemStateFiniteExact.fixClock]
    rw [if_neg e]
    congr 2
    funext x
    by_cases hx : x = a <;> simp [hx]

/-- `WriteLastByte_aux` steps for the offsets `k, ..., m - 1`, ending in `Skip`:
Flapjack infrastructure for `evaluate_WriteLastBytes`. -/
private def writeChain {width : Nat} [NeZero width] (av bv nv : Nat) (k m : Nat) :
    WordLangProgHOL (BitVec width) :=
  if k < m then writeLastByteAux (BitVec.ofNat width k) av bv nv (writeChain av bv nv (k + 1) m)
  else .skip
termination_by m - k

private theorem writeChain_lt {width : Nat} [NeZero width] (av bv nv k m : Nat) (h : k < m) :
    (writeChain av bv nv k m : WordLangProgHOL (BitVec width)) =
      writeLastByteAux (BitVec.ofNat width k) av bv nv (writeChain av bv nv (k + 1) m) := by
  rw [writeChain, if_pos h]

private theorem writeChain_ge {width : Nat} [NeZero width] (av bv nv k m : Nat) (h : ¬ k < m) :
    (writeChain av bv nv k m : WordLangProgHOL (BitVec width)) = .skip := by
  rw [writeChain, if_neg h]

private theorem writeLastBytes_eq_chain {width : Nat} [NeZero width] (good : goodDimindex width)
    (av bv nv : Nat) :
    (writeLastBytes av bv nv : WordLangProgHOL (BitVec width)) = writeChain av bv nv 0 (width / 8) := by
  rcases good with rfl | rfl <;>
  · simp (disch := decide) only [writeLastBytes, writeChain_lt, writeChain_ge]
    rfl

private theorem toNat_mod_add_aligned {width : Nat} [NeZero width] (good : goodDimindex width)
    (a : BitVec width) (hal : holByteAligned a = true) (k : Nat) (hk : k < width / 8) :
    (a + BitVec.ofNat width k).toNat % (width / 8) =
      ((0 : BitVec width) + BitVec.ofNat width k).toNat % (width / 8) := by
  have hp : 2 ^ holLOG2 (width / 8) = width / 8 := by
    rcases good with rfl | rfl
    · rw [holLOG2_eq_log2 (by decide)]; decide
    · rw [holLOG2_eq_log2 (by decide)]; decide
  have a0 : a.toNat % (width / 8) = 0 := by
    have := (holAligned_iff _ a).1 hal
    rwa [hp] at this
  have alt := a.isLt
  rcases good with rfl | rfl <;>
  · rw [show ∀ x : BitVec _, (0 : BitVec _) + x = x from fun x => by simp]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at a0 alt ⊢
    norm_num at a0 alt hk ⊢
    omega

private theorem holByteAlign_add_aligned {width : Nat} [NeZero width] (good : goodDimindex width)
    (a : BitVec width) (hal : holByteAligned a = true) (k : Nat) (hk : k < width / 8) :
    holByteAlign (a + BitVec.ofNat width k) = a := by
  have hp : 2 ^ holLOG2 (width / 8) = width / 8 := by
    rcases good with rfl | rfl
    · rw [holLOG2_eq_log2 (by decide)]; decide
    · rw [holLOG2_eq_log2 (by decide)]; decide
  have a0 : a.toNat % (width / 8) = 0 := by
    have := (holAligned_iff _ a).1 hal
    rwa [hp] at this
  apply BitVec.eq_of_toNat_eq
  rw [holByteAlign_toNat good]
  have alt := a.isLt
  rcases good with rfl | rfl <;>
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at a0 alt ⊢
    norm_num at a0 alt hk ⊢
    omega

private theorem evaluate_writeChain {width : Nat} [NeZero width] {C F : Type}
    (good : goodDimindex width) (s : WordSemStateFiniteExact width C F) (av bv nv : Nat)
    (a b n w : BitVec width)
    (ha : WordSemStateFiniteExact.getVar av s = some (.word a))
    (hb : WordSemStateFiniteExact.getVar bv s = some (.word b))
    (hn : WordSemStateFiniteExact.getVar nv s = some (.word n))
    (hdom : s.mdomain a = true) (hal : holByteAligned a = true)
    (hlt : n.toNat < width / 8) :
    ∀ j k, k + j = n.toNat →
      WordSemStateFiniteExact.evaluate (writeChain av bv nv k (width / 8))
          (withWordAt s a (lastBytes k (b.setWidth 8) 0 w s.be)) =
        (none, withWordAt s a (lastBytes n.toNat (b.setWidth 8) 0 w s.be)) := by
  have nlt : n.toNat < 2 ^ width := n.isLt
  intro j
  induction j with
  | zero =>
    intro k hk
    subst hk
    rw [writeChain, if_pos hlt,
      evaluate_writeLastByteAux good s av bv nv a b n ha hb hn hdom _ _ _
        (holByteAlign_add_aligned good a hal _ hlt)]
    simp
  | succ j ih =>
    intro k hk
    have klt : k < width / 8 := by omega
    have ne : n ≠ BitVec.ofNat width k := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      omega
    rw [writeChain, if_pos klt,
      evaluate_writeLastByteAux good s av bv nv a b n ha hb hn hdom _ _ _
        (holByteAlign_add_aligned good a hal _ klt), if_neg ne,
      setByte_changeAddress _ ((0 : BitVec width) + BitVec.ofNat width k) _ _ _
        (toNat_mod_add_aligned good a hal k klt),
      ← lastBytes_succ good _ w s.be k 0 (by simp; omega)]
    exact ih (k + 1) (by omega)

open Classical in
/-- `WriteLastBytes` writes the low `n` byte lanes of the aligned word at `a`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_WriteLastBytes"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_writeLastBytes {width : Nat} [NeZero width] {C F : Type} (av bv nv : Nat)
    (s : WordSemStateFiniteExact width C F) (a b n w : BitVec width) :
    goodDimindex width → n.toNat < width / 8 →
    WordSemStateFiniteExact.getVars [av, bv, nv] s = some [.word a, .word b, .word n] →
    holByteAligned a = true → s.mdomain a = true → s.memory a = .word w →
    WordSemStateFiniteExact.evaluate (writeLastBytes av bv nv) s =
      (none, { s with memory := fun x =>
        if x = a then .word (lastBytes n.toNat (b.setWidth 8) 0 w s.be) else s.memory x }) := by
  intro good hlt hv hal hdom hmem
  obtain ⟨ha, hb, hn⟩ : WordSemStateFiniteExact.getVar av s = some (.word a) ∧
      WordSemStateFiniteExact.getVar bv s = some (.word b) ∧
      WordSemStateFiniteExact.getVar nv s = some (.word n) := by
    cases h1 : WordSemStateFiniteExact.getVar av s <;>
      cases h2 : WordSemStateFiniteExact.getVar bv s <;>
      cases h3 : WordSemStateFiniteExact.getVar nv s <;>
      simp_all [WordSemStateFiniteExact.getVars]
  have start : withWordAt s a (lastBytes 0 (b.setWidth 8) 0 w s.be) = s := by
    have : (fun x => if x = a then WordLocW.word w else s.memory x) = s.memory := by
      funext x; by_cases hx : x = a <;> simp [hx, hmem]
    simp [withWordAt, lastBytes, this]
  rw [writeLastBytes_eq_chain good]
  conv_lhs => rw [← start]
  exact evaluate_writeChain good s av bv nv a b n w ha hb hn hdom hal hlt n.toNat 0 (by omega)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
