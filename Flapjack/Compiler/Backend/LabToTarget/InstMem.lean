import Flapjack.Compiler.Backend.LabToTarget.InstFrame
import Flapjack.Compiler.Backend.LabToTarget.InstAlignment
import Flapjack.Compiler.Backend.Semantics.WordSem
import Mathlib.Data.BitVec
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Memory-instruction case of the original `Inst_lemma`
(lab_to_targetProofScript.sml:2242-2878). The source side uses the reviewed
wordSem byte helpers; their agreement with the HOL `byte` library renderings
and the target `read_mem_word`/`write_mem_word` computations at the 32- and
64-bit dimensions allowed by `good_dimindex` are Flapjack infrastructure
(HOL rewrites with `read_mem_word_compute`/`write_mem_word_compute`). -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.HolByte
open Classical

/-! ### Agreement of the byte-codec renderings -/

theorem getByteHOL8_eq {width : Nat} [NeZero width] (a v : BitVec width) (be : Bool) :
    getByteHOL8 a v be = getByte a v be := rfl

theorem riscvByteAlignHOL_eq {width : Nat} [NeZero width] (h : goodDimindex width)
    (a : BitVec width) : riscvByteAlignHOL a = holByteAlign a := by
  apply BitVec.eq_of_toNat_eq
  rw [holByteAlign_toNat h]
  have hp : 2 ^ Nat.log2 (width / 8) = width / 8 := by
    rcases h with rfl | rfl <;> decide
  simp only [riscvByteAlignHOL, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, hp]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) a.isLt

theorem riscvAlignedHOL_iff {width : Nat} [NeZero width] (k : Nat) (a : BitVec width) :
    riscvAlignedHOL k a = true ↔ holAligned k a = true := by
  simp only [riscvAlignedHOL, holAligned, holAlign_eq_shift, decide_eq_true_eq]

theorem setByteHOL8_eq {width : Nat} [NeZero width] (a : BitVec width) (b : BitVec 8)
    (v : BitVec width) (be : Bool) : setByteHOL8 a b v be = setByte a b v be := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_setByte a b v be j hj]
  have hidx : byteIndexHOL a be = byteIndex a be := rfl
  simp only [setByteHOL8, hidx, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hj, decide_true,
    Bool.true_and]
  by_cases h1 : j < byteIndex a be
  · simp [h1, show ¬ byteIndex a be + 8 ≤ j by omega, show ¬ byteIndex a be ≤ j by omega]
  · by_cases h2 : j < byteIndex a be + 8
    · have : (255 : Nat).testBit (j - byteIndex a be) = true := by
        have : j - byteIndex a be < 8 := by omega
        interval_cases (j - byteIndex a be) <;> decide
      simp [h1, this, show ¬ byteIndex a be + 8 ≤ j by omega,
        show byteIndex a be ≤ j by omega, show j - byteIndex a be < width by omega]
    · have : (255 : Nat).testBit (j - byteIndex a be) = false := by
        apply Nat.testBit_lt_two_pow
        calc 255 < 2 ^ 8 := by decide
          _ ≤ 2 ^ (j - byteIndex a be) := Nat.pow_le_pow_right (by decide) (by omega)
      simp [h1, this, show byteIndex a be + 8 ≤ j by omega,
        show byteIndex a be ≤ j by omega,
        BitVec.getLsbD_of_ge b (j - byteIndex a be) (by omega)]

/-! ### Target word reads and writes -/

/-- Value assembled by `read_mem_word`. -/
def rmwVal {width : Nat} [NeZero width] {rw : Nat} (be : Bool) (mem : BitVec width → BitVec 8)
    (a : BitVec width) : Nat → BitVec rw
  | 0 => 0
  | n + 1 => (rmwVal be mem (if be then a - 1 else a + 1) n <<< (8 : Nat)) ||| (mem a).setWidth rw

/-- Whether every address touched by `read_mem_word`/`write_mem_word` is in
the domain. -/
noncomputable def rmwOk {width : Nat} [NeZero width] (be : Bool) (dom : BitVec width → Prop)
    (a : BitVec width) : Nat → Bool
  | 0 => true
  | n + 1 => rmwOk be dom (if be then a - 1 else a + 1) n && decide (dom a)

theorem assertState_assertState {width : Nat} [NeZero width] (c c' : Bool)
    (s : AsmState width) :
    AsmSem.assertState c (AsmSem.assertState c' s) = AsmSem.assertState (c' && c) s := by
  cases c <;> cases c' <;> simp [AsmSem.assertState]

theorem readMemWord_eq {width : Nat} [NeZero width] {rw : Nat} [NeZero rw]
    (a : BitVec width) (n : Nat) (s : AsmState width) :
    AsmSem.readMemWord (resultWidth := rw) a n s =
      (rmwVal s.be s.mem a n, AsmSem.assertState (rmwOk s.be s.memDomain a n) s) := by
  induction n generalizing a with
  | zero => simp [AsmSem.readMemWord, rmwVal, rmwOk, AsmSem.assertState]
  | succ n ih =>
    rw [AsmSem.readMemWord_succ, ih]
    simp only [rmwVal, rmwOk, AsmSem.readMem, assertState_assertState]
    rfl

/-- Memory written by `write_mem_word`. -/
def wmwMem {width : Nat} [NeZero width] {vw : Nat} (be : Bool) (mem : BitVec width → BitVec 8)
    (a : BitVec width) : Nat → BitVec vw → BitVec width → BitVec 8
  | 0, _ => mem
  | n + 1, w => fun x => if x = a then w.setWidth 8
      else wmwMem be mem (if be then a - 1 else a + 1) n (w >>> (8 : Nat)) x

theorem writeMemWord_eq {width : Nat} [NeZero width] {vw : Nat} [NeZero vw]
    (a : BitVec width) (n : Nat) (w : BitVec vw) (s : AsmState width) :
    AsmSem.writeMemWord a n w s =
      AsmSem.assertState (rmwOk s.be s.memDomain a n)
        { s with mem := wmwMem s.be s.mem a n w } := by
  induction n generalizing a w with
  | zero => cases s; simp [AsmSem.writeMemWord, wmwMem, rmwOk, AsmSem.assertState]
  | succ n ih =>
    rw [AsmSem.writeMemWord_succ, ih]
    simp only [rmwOk, wmwMem, AsmSem.updMem, AsmSem.assertState]
    congr 1
    generalize rmwOk (width := width) _ _ _ _ = x
    by_cases hd : s.memDomain a <;> cases x <;> simp [hd]

/-- Address of the `k`-th byte visited from `B` in the given direction. -/
def stepAddr {width : Nat} [NeZero width] (be : Bool) (B : BitVec width) (k : Nat) :
    BitVec width :=
  if be then B - BitVec.ofNat width k else B + BitVec.ofNat width k

theorem stepAddr_succ {width : Nat} [NeZero width] (be : Bool) (B : BitVec width) (k : Nat) :
    stepAddr be (if be then B - 1 else B + 1) k = stepAddr be B (k + 1) := by
  have h1 : BitVec.ofNat width (k + 1) = BitVec.ofNat width k + 1 := by
    rw [BitVec.ofNat_add]; rfl
  cases be <;> simp only [stepAddr, Bool.false_eq_true, ↓reduceIte, h1] <;> ring

theorem stepAddr_zero {width : Nat} [NeZero width] (be : Bool) (B : BitVec width) :
    stepAddr be B 0 = B := by
  cases be <;> simp [stepAddr]

/-- Every bit of a read word is a bit of the byte it came from. -/
theorem getLsbD_rmwVal {width : Nat} [NeZero width] {rw : Nat} (be : Bool)
    (mem : BitVec width → BitVec 8) (B : BitVec width) (n j : Nat) (_hrw : 4 ≤ rw)
    (hj : j < rw) :
    (rmwVal (rw := rw) be mem B n).getLsbD j =
      (decide (j / 8 < n) && (mem (stepAddr be B (j / 8))).getLsbD (j % 8)) := by
  induction n generalizing B j with
  | zero => simp [rmwVal]
  | succ n ih =>
    simp only [rmwVal, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    by_cases hj8 : j < 8
    · have h0 : j / 8 = 0 := Nat.div_eq_of_lt hj8
      simp [hj8, h0, Nat.mod_eq_of_lt hj8, stepAddr_zero]
    · rw [ih _ (j - 8) (by omega), stepAddr_succ]
      have h1 : (j - 8) / 8 + 1 = j / 8 := by omega
      have h2 : (j - 8) % 8 = j % 8 := by omega
      simp only [hj8, decide_false, Bool.not_false, Bool.true_and, h1, h2,
        BitVec.getLsbD_of_ge (mem B) j (by omega), Bool.or_false]
      congr 1
      simp only [decide_eq_decide]
      omega

/-- Bytes written by `write_mem_word`: the `k`-th visited address receives
the `k`-th byte of the value. -/
theorem wmwMem_step {width : Nat} [NeZero width] {vw : Nat} (be : Bool)
    (mem : BitVec width → BitVec 8) (B : BitVec width) (n : Nat) (w : BitVec vw) (k : Nat)
    (_hvw : 4 ≤ vw) (hk : k < n) (hn : n ≤ 2 ^ width) :
    wmwMem be mem B n w (stepAddr be B k) = (w >>> (8 * k)).setWidth 8 := by
  induction n generalizing B w k with
  | zero => omega
  | succ n ih =>
    simp only [wmwMem]
    cases k with
    | zero => simp [stepAddr_zero]
    | succ k =>
      have hne : stepAddr be B (k + 1) ≠ B := by
        have hlt : k + 1 < 2 ^ width := by omega
        intro h
        have h' : BitVec.ofNat width (k + 1) = 0 := by
          cases be <;> simp only [stepAddr, Bool.false_eq_true, ↓reduceIte] at h
          · linear_combination h
          · linear_combination -h
        have := congrArg BitVec.toNat h'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
        simp at this
      rw [if_neg hne, ← stepAddr_succ, ih _ _ k (by omega) (by omega)]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        hi, decide_true, Bool.true_and]
      congr 1
      omega

/-- Addresses never visited by `write_mem_word` keep their bytes. -/
theorem wmwMem_other {width : Nat} [NeZero width] {vw : Nat} (be : Bool)
    (mem : BitVec width → BitVec 8) (B : BitVec width) (n : Nat) (w : BitVec vw)
    (x : BitVec width) (hx : ∀ k < n, x ≠ stepAddr be B k) : wmwMem be mem B n w x = mem x := by
  induction n generalizing B w with
  | zero => rfl
  | succ n ih =>
    simp only [wmwMem]
    rw [if_neg (by simpa [stepAddr_zero] using hx 0 (by omega))]
    apply ih
    intro k hk
    rw [stepAddr_succ]
    exact hx (k + 1) (by omega)

/-- Every visited address is in the domain exactly when `rmwOk` holds. -/
theorem rmwOk_iff {width : Nat} [NeZero width] (be : Bool) (dom : BitVec width → Prop)
    (B : BitVec width) (n : Nat) :
    rmwOk be dom B n = true ↔ ∀ k < n, dom (stepAddr be B k) := by
  induction n generalizing B with
  | zero => simp [rmwOk]
  | succ n ih =>
    simp only [rmwOk, Bool.and_eq_true, ih, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      cases k with
      | zero => simpa [stepAddr_zero] using h2
      | succ k => rw [← stepAddr_succ]; exact h1 k (by omega)
    · intro h
      refine ⟨fun k hk => ?_, by simpa [stepAddr_zero] using h 0 (by omega)⟩
      rw [stepAddr_succ]; exact h (k + 1) (by omega)

/-! ### Byte positions inside an aligned word -/

theorem goodDimindex_four_le {width : Nat} (hw : goodDimindex width) : 4 ≤ width := by
  rcases hw with rfl | rfl <;> decide

/-- Offsets inside a word from a word-aligned address do not wrap. -/
theorem aligned_add_toNat {width : Nat} [NeZero width] (hw : goodDimindex width)
    (A : BitVec width) (hA : A.toNat % (width / 8) = 0) (m : Nat) (hm : m < width / 8) :
    (A + BitVec.ofNat width m).toNat = A.toNat + m := by
  rcases hw with rfl | rfl <;> simp only [Nat.reduceDiv] at hA hm <;>
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] <;> bv_omega

/-- The byte index of the `m`-th byte of a word-aligned address. -/
theorem byteIndex_aligned_add {width : Nat} [NeZero width] (hw : goodDimindex width)
    (A : BitVec width) (hA : A.toNat % (width / 8) = 0) (m : Nat) (hm : m < width / 8)
    (be : Bool) :
    byteIndex (A + BitVec.ofNat width m) be =
      if be then 8 * (width / 8 - 1 - m) else 8 * m := by
  have hd : 0 < width / 8 := by rcases hw with rfl | rfl <;> decide
  have hmod : (A + BitVec.ofNat width m).toNat % (width / 8) = m := by
    rw [aligned_add_toNat hw A hA m hm, Nat.add_mod, hA, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hm]
  cases be <;> simp only [byteIndex, hmod, Bool.false_eq_true, ↓reduceIte]

/-- Reading the bytes of a word from its aligned address recovers the word. -/
theorem rmwVal_word {width : Nat} [NeZero width] (hw : goodDimindex width) (be : Bool)
    (mem : BitVec width → BitVec 8) (A v : BitVec width) (hA : A.toNat % (width / 8) = 0)
    (hm : ∀ m < width / 8, mem (A + BitVec.ofNat width m) =
      getByte (A + BitVec.ofNat width m) v be) :
    rmwVal (rw := width) be mem
      (if be then A + BitVec.ofNat width (width / 8 - 1) else A) (width / 8) = v := by
  have h8d : width = 8 * (width / 8) := by rcases hw with rfl | rfl <;> rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_rmwVal be mem _ _ j (goodDimindex_four_le hw) hj]
  have hjd : j / 8 < width / 8 := by omega
  have haddr : stepAddr be (if be then A + BitVec.ofNat width (width / 8 - 1) else A) (j / 8) =
      A + BitVec.ofNat width (if be then width / 8 - 1 - j / 8 else j / 8) := by
    cases be
    · simp [stepAddr]
    · simp only [stepAddr, ↓reduceIte]
      have : BitVec.ofNat width (width / 8 - 1) =
          BitVec.ofNat width (width / 8 - 1 - j / 8) + BitVec.ofNat width (j / 8) := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel (by omega)]
      rw [this]; ring
  have hlt : (if be then width / 8 - 1 - j / 8 else j / 8) < width / 8 := by
    split <;> omega
  rw [decide_eq_true hjd, Bool.true_and, haddr, hm _ hlt, getLsbD_getByte _ _ _ _
    (Nat.mod_lt _ (by decide)), byteIndex_aligned_add hw A hA _ hlt]
  congr 1
  cases be <;> simp <;> omega

/-- Every address is its byte-aligned base plus its offset in the word. -/
theorem holByteAlign_add_mod {width : Nat} [NeZero width] (hw : goodDimindex width)
    (x : BitVec width) :
    holByteAlign x + BitVec.ofNat width (x.toNat % (width / 8)) = x := by
  rcases hw with h | h <;> subst h
  · exact byte_align_32_eq x rfl
  · exact byte_align_64_eq x rfl

/-- A byte-aligned base is word-aligned. -/
theorem holByteAlign_toNat_mod {width : Nat} [NeZero width] (hw : goodDimindex width)
    (x : BitVec width) : (holByteAlign x).toNat % (width / 8) = 0 := by
  rw [holByteAlign_toNat hw]
  exact Nat.mul_mod_left _ _

/-- The byte-aligned base of an offset inside an aligned word. -/
theorem holByteAlign_aligned_add {width : Nat} [NeZero width] (hw : goodDimindex width)
    (A : BitVec width) (hA : A.toNat % (width / 8) = 0) (m : Nat) (hm : m < width / 8) :
    holByteAlign (A + BitVec.ofNat width m) = A := by
  have hd : 0 < width / 8 := by rcases hw with rfl | rfl <;> decide
  apply BitVec.eq_of_toNat_eq
  rw [holByteAlign_toNat hw, aligned_add_toNat hw A hA m hm]
  have := Nat.div_add_mod A.toNat (width / 8)
  rw [hA, Nat.add_zero] at this
  rw [show A.toNat + m = m + (width / 8) * (A.toNat / (width / 8)) by omega,
    Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hm, Nat.zero_add]
  rw [Nat.mul_comm] at this
  exact this

/-- The addresses visited when accessing a whole word from its aligned
address are exactly the bytes of that word. -/
theorem stepAddr_word {width : Nat} [NeZero width] (be : Bool)
    (A : BitVec width) (k : Nat) (hk : k < width / 8) :
    stepAddr be (if be then A + BitVec.ofNat width (width / 8 - 1) else A) k =
      A + BitVec.ofNat width (if be then width / 8 - 1 - k else k) := by
  cases be
  · simp [stepAddr]
  · simp only [stepAddr, ↓reduceIte]
    have : BitVec.ofNat width (width / 8 - 1) =
        BitVec.ofNat width (width / 8 - 1 - k) + BitVec.ofNat width k := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel (by omega)]
    rw [this]; ring

/-- Writing a whole word at its aligned address stores its bytes there. -/
theorem wmwMem_word {width : Nat} [NeZero width] (hw : goodDimindex width) (be : Bool)
    (mem : BitVec width → BitVec 8) (A v : BitVec width) (hA : A.toNat % (width / 8) = 0)
    (m : Nat) (hm : m < width / 8) :
    wmwMem be mem (if be then A + BitVec.ofNat width (width / 8 - 1) else A) (width / 8) v
      (A + BitVec.ofNat width m) = getByte (A + BitVec.ofNat width m) v be := by
  have hd : width / 8 ≤ 2 ^ width := by rcases hw with rfl | rfl <;> decide
  have hk : (if be then width / 8 - 1 - m else m) < width / 8 := by split <;> omega
  have hsa := stepAddr_word be A _ hk
  have hm' : (if be then width / 8 - 1 - (if be then width / 8 - 1 - m else m) else
      (if be then width / 8 - 1 - m else m)) = m := by cases be <;> first | (simp; done) | (simp; omega)
  rw [hm'] at hsa
  conv_lhs => rw [← hsa]
  rw [wmwMem_step be mem _ _ v _ (goodDimindex_four_le hw) hk hd]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_getByte _ _ _ _ hi, byteIndex_aligned_add hw A hA m hm]
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]
  cases be <;> simp

/-- Writing a whole word leaves the bytes of every other word unchanged. -/
theorem wmwMem_word_other {width : Nat} [NeZero width] (hw : goodDimindex width) (be : Bool)
    (mem : BitVec width → BitVec 8) (A v : BitVec width) (hA : A.toNat % (width / 8) = 0)
    (x : BitVec width) (hx : holByteAlign x ≠ A) :
    wmwMem be mem (if be then A + BitVec.ofNat width (width / 8 - 1) else A) (width / 8) v x =
      mem x := by
  apply wmwMem_other
  intro k hk heq
  have hk' : (if be then width / 8 - 1 - k else k) < width / 8 := by split <;> omega
  rw [stepAddr_word be A k hk] at heq
  exact hx (heq ▸ holByteAlign_aligned_add hw A hA _ hk')

/-! ### Target memory operations in closed form -/

theorem asm_memLoad_eq {width : Nat} [NeZero width] (n r : Nat) (a : HolAddr width)
    (s : AsmState width) :
    AsmSem.memLoad n r a s =
      AsmSem.assertState (holAligned (holLOG2 n) (AsmSem.addrHOL a s))
        (AsmSem.updReg r (rmwVal s.be s.mem (if s.be then AsmSem.addrHOL a s +
            BitVec.ofNat width (n - 1) else AsmSem.addrHOL a s) n)
          (AsmSem.assertState (rmwOk s.be s.memDomain (if s.be then AsmSem.addrHOL a s +
            BitVec.ofNat width (n - 1) else AsmSem.addrHOL a s) n) s)) := by
  simp only [AsmSem.memLoad, readMemWord_eq]

theorem asm_memStore_eq {width : Nat} [NeZero width] (n r : Nat) (a : HolAddr width)
    (s : AsmState width) :
    AsmSem.memStore n r a s =
      AsmSem.assertState (holAligned (holLOG2 n) (AsmSem.addrHOL a s))
        (AsmSem.assertState (rmwOk s.be s.memDomain (if s.be then AsmSem.addrHOL a s +
            BitVec.ofNat width (n - 1) else AsmSem.addrHOL a s) n)
          { s with mem := wmwMem s.be s.mem (if s.be then AsmSem.addrHOL a s +
            BitVec.ofNat width (n - 1) else AsmSem.addrHOL a s) n (AsmSem.readReg r s) }) := by
  simp only [AsmSem.memStore, writeMemWord_eq]

/-- `aligned (LOG2 (dimindex DIV 8))` is word alignment at a good dimension. -/
theorem holAligned_word_iff {width : Nat} [NeZero width] (hw : goodDimindex width)
    (A : BitVec width) :
    holAligned (holLOG2 (width / 8)) A = true ↔ A.toNat % (width / 8) = 0 := by
  have hp : 2 ^ holLOG2 (width / 8) = width / 8 := by
    rcases hw with rfl | rfl
    · rw [holLOG2_eq_log2 (by decide)]; decide
    · rw [holLOG2_eq_log2 (by decide)]; decide
  rw [holAligned_iff, hp]

/-- A word-aligned address is its own byte-aligned base. -/
theorem holByteAlign_of_aligned {width : Nat} [NeZero width] (hw : goodDimindex width)
    (A : BitVec width) (hA : A.toNat % (width / 8) = 0) : holByteAlign A = A := by
  have := holByteAlign_aligned_add hw A hA 0 (by rcases hw with rfl | rfl <;> decide)
  simpa using this

/-- The related target bytes of a source word lying at a word-aligned address. -/
theorem stateMem_word {width : Nat} [NeZero width] {C F : Type} (hw : goodDimindex width)
    (p : BitVec width) (labs : Spt (Spt Nat)) (s1 : LabSem.State width C F)
    (t1 : AsmState width)
    (hmem : ∀ a, s1.memDomain (holByteAlign a) = true → t1.memDomain a ∧
      s1.memDomain a = true ∧ wordLocValByte p labs s1.memory a s1.be = some (t1.mem a))
    (A : BitVec width) (hA : A.toNat % (width / 8) = 0) (hdom : s1.memDomain A = true) :
    ∃ v, wordLocVal p labs (s1.memory A) = some v ∧
      ∀ m < width / 8, t1.memDomain (A + BitVec.ofNat width m) ∧
        t1.mem (A + BitVec.ofNat width m) = getByte (A + BitVec.ofNat width m) v s1.be := by
  have hal := holByteAlign_of_aligned hw A hA
  obtain ⟨-, -, hb⟩ := hmem A (by rw [hal]; exact hdom)
  rw [wordLocValByte, hal] at hb
  cases hv : wordLocVal p labs (s1.memory A) with
  | none => rw [hv] at hb; exact absurd hb (by simp)
  | some v =>
    refine ⟨v, rfl, fun m hm => ?_⟩
    have hal' := holByteAlign_aligned_add hw A hA m hm
    obtain ⟨h1, -, h3⟩ := hmem (A + BitVec.ofNat width m) (by rw [hal']; exact hdom)
    rw [wordLocValByte, hal', hv] at h3
    exact ⟨h1, (Option.some.inj h3).symm⟩

/-- Facts of the related pre-states consumed by the memory cases. -/
structure MemCtx {width : Nat} [NeZero width] {C F : Type} (p : BitVec width)
    (labs : Spt (Spt Nat)) (s1 : LabSem.State width C F) (t1 : AsmState width) : Prop where
  good : goodDimindex width
  regs : ∀ r, wordLocVal p labs (s1.regs r) = some (t1.regs r)
  fp : ∀ r, s1.fpRegs r = t1.fpRegs r
  mem : ∀ a, s1.memDomain (holByteAlign a) = true → t1.memDomain a ∧
    s1.memDomain a = true ∧ wordLocValByte p labs s1.memory a s1.be = some (t1.mem a)
  tfailed : t1.failed = false
  be : s1.be = t1.be

/-- The source and target compute the same address from a word base. -/
theorem MemCtx.addr {width : Nat} [NeZero width] {C F : Type} {p : BitVec width}
    {labs : Spt (Spt Nat)} {s1 : LabSem.State width C F} {t1 : AsmState width}
    (h : MemCtx p labs s1 t1) (base : Nat) (off wb : BitVec width)
    (hb : s1.regs base = .word wb) :
    AsmSem.addrHOL (.addr base off) t1 = wb + off := by
  simp [AsmSem.addrHOL, AsmSem.readReg, wordLocVal_word_target (h.regs base) hb]

theorem instSim_load {width : Nat} [NeZero width] {C F : Type} {p : BitVec width}
    {labs : Spt (Spt Nat)} {s1 : LabSem.State width C F} {t1 : AsmState width}
    (h : MemCtx p labs s1 t1) (r : Nat) (addr : HolAddr width)
    (hf : ¬ (asmInst (.mem .load r addr) s1).failed) :
    InstSim p labs (.mem .load r addr) s1 t1 := by
  obtain ⟨base, off⟩ := addr
  simp only [asmInst, LabSem.memOp, LabSem.memLoad, LabSem.addrValue] at hf
  cases hb : s1.regs base with
  | loc _ _ => simp [hb, LabSem.assertState] at hf
  | word wb =>
    simp only [hb, LabSem.assertState, LabSem.updReg, Bool.not_and, Bool.or_eq_true,
      Bool.not_eq_true', not_or] at hf
    obtain ⟨⟨hal, hdom⟩, -⟩ := hf
    simp only [decide_eq_false_iff_not, not_not, Bool.not_eq_false] at hal hdom
    obtain ⟨v, hv, hbytes⟩ := stateMem_word h.good p labs s1 t1 h.mem _ hal hdom
    have hrd : rmwVal t1.be t1.mem (if t1.be then wb + off + BitVec.ofNat width (width / 8 - 1)
        else wb + off) (width / 8) = v :=
      rmwVal_word h.good t1.be t1.mem _ v hal (fun m hm => by rw [(hbytes m hm).2, h.be])
    have hok : rmwOk t1.be t1.memDomain (if t1.be then wb + off +
        BitVec.ofNat width (width / 8 - 1) else wb + off) (width / 8) = true := by
      rw [rmwOk_iff]
      intro k hk
      rw [stepAddr_word t1.be _ k hk]
      exact (hbytes _ (by split <;> omega)).1
    have haln := (holAligned_word_iff h.good (wb + off)).2 hal
    have htarget : AsmSem.instUpd (.mem .load r (.addr base off)) t1 = AsmSem.updReg r v t1 := by
      simp only [AsmSem.instUpd, AsmSem.memOp, asm_memLoad_eq, h.addr base off wb hb, hrd,
        hok, haln]
      simp [AsmSem.assertState, AsmSem.updReg, h.tfailed]
    have hsrc : asmInst (.mem .load r (.addr base off)) s1 =
        LabSem.assertState (decide ((wb + off).toNat % (width / 8) = 0) && s1.memDomain (wb + off))
          (LabSem.updReg r (s1.memory (wb + off)) s1) := by
      simp [asmInst, LabSem.memOp, LabSem.memLoad, LabSem.addrValue, hb]
    unfold InstSim
    rw [htarget, hsrc]
    refine ⟨by simp [AsmSem.updReg, h.tfailed], fun _ _ => rfl, fun r' => ?_, h.fp, ?_⟩
    · simp only [LabSem.assertState, LabSem.updReg, AsmSem.updReg]
      split_ifs
      · exact hv
      · exact h.regs r'
    · intro x hx
      exact (h.mem x hx).2.2

theorem instSim_store {width : Nat} [NeZero width] {C F : Type} {p : BitVec width}
    {labs : Spt (Spt Nat)} {s1 : LabSem.State width C F} {t1 : AsmState width}
    (h : MemCtx p labs s1 t1) (r : Nat) (addr : HolAddr width)
    (hf : ¬ (asmInst (.mem .store r addr) s1).failed) :
    InstSim p labs (.mem .store r addr) s1 t1 := by
  obtain ⟨base, off⟩ := addr
  simp only [asmInst, LabSem.memOp, LabSem.memStore, LabSem.addrValue] at hf
  cases hb : s1.regs base with
  | loc _ _ => simp [hb, LabSem.assertState] at hf
  | word wb =>
    simp only [hb, LabSem.assertState, LabSem.updMem, Bool.not_and, Bool.or_eq_true,
      Bool.not_eq_true', not_or] at hf
    obtain ⟨⟨hal, hdom⟩, -⟩ := hf
    simp only [decide_eq_false_iff_not, not_not, Bool.not_eq_false] at hal hdom
    set A := wb + off with hAdef
    obtain ⟨_, -, hbytes⟩ := stateMem_word h.good p labs s1 t1 h.mem A hal hdom
    have hok : rmwOk t1.be t1.memDomain (if t1.be then A + BitVec.ofNat width (width / 8 - 1)
        else A) (width / 8) = true := by
      rw [rmwOk_iff]
      intro k hk
      rw [stepAddr_word t1.be _ k hk]
      exact (hbytes _ (by split <;> omega)).1
    have haln := (holAligned_word_iff h.good A).2 hal
    have htarget : AsmSem.instUpd (.mem .store r (.addr base off)) t1 =
        { t1 with mem := wmwMem t1.be t1.mem (if t1.be then A +
            BitVec.ofNat width (width / 8 - 1) else A) (width / 8) (t1.regs r) } := by
      simp only [AsmSem.instUpd, AsmSem.memOp, asm_memStore_eq, h.addr base off wb hb,
        ← hAdef, hok, haln, AsmSem.readReg]
      simp [AsmSem.assertState, h.tfailed]
    have hsrc : asmInst (.mem .store r (.addr base off)) s1 =
        LabSem.assertState (decide (A.toNat % (width / 8) = 0) && s1.memDomain A)
          (LabSem.updMem A (s1.regs r) s1) := by
      simp [asmInst, LabSem.memOp, LabSem.memStore, LabSem.addrValue, hb, hAdef]
    -- Addresses whose word is not the stored word are untouched on both sides.
    have hother : ∀ x, holByteAlign x ≠ A →
        wmwMem t1.be t1.mem (if t1.be then A + BitVec.ofNat width (width / 8 - 1) else A)
          (width / 8) (t1.regs r) x = t1.mem x :=
      fun x hx => wmwMem_word_other h.good t1.be t1.mem A _ hal x hx
    unfold InstSim
    rw [htarget, hsrc]
    refine ⟨by simp [h.tfailed], fun x hx => ?_, h.regs, h.fp, fun x hx => ?_⟩
    · apply hother
      intro hxa
      exact hx (h.mem x (by rw [hxa]; exact hdom)).2.1
    · simp only [LabSem.assertState, LabSem.updMem]
      by_cases hxa : holByteAlign x = A
      · have hx' := holByteAlign_add_mod h.good x
        rw [hxa] at hx'
        have hlt : x.toNat % (width / 8) < width / 8 :=
          Nat.mod_lt _ (by rcases h.good with h' | h' <;> rw [h'] <;> decide)
        rw [wordLocValByte, hxa, if_pos rfl]
        obtain ⟨w, hw⟩ : ∃ w, wordLocVal p labs (s1.regs r) = some w := ⟨_, h.regs r⟩
        rw [h.regs r]
        conv_rhs => rw [← hx']
        rw [wmwMem_word h.good t1.be t1.mem A _ hal _ hlt, hx', h.be]
      · rw [wordLocValByte, if_neg hxa, hother x hxa]
        exact (h.mem x hx).2.2

theorem holLOG2_one : holLOG2 1 = 0 := by
  rw [holLOG2_eq_log2 (by decide)]; rfl

theorem holAligned_zero {width : Nat} [NeZero width] (A : BitVec width) :
    holAligned 0 A = true := by
  rw [holAligned_iff]; exact Nat.mod_one _

/-- A source word cell read through its domain-aligned base relates each of
its bytes to the target memory. -/
theorem MemCtx.byte {width : Nat} [NeZero width] {C F : Type} {p : BitVec width}
    {labs : Spt (Spt Nat)} {s1 : LabSem.State width C F} {t1 : AsmState width}
    (h : MemCtx p labs s1 t1) (x v : BitVec width)
    (hv : s1.memory (holByteAlign x) = .word v) (hdom : s1.memDomain (holByteAlign x) = true) :
    t1.memDomain x ∧ s1.memDomain x = true ∧ t1.mem x = getByte x v s1.be := by
  obtain ⟨h1, h2, h3⟩ := h.mem x hdom
  rw [wordLocValByte, hv] at h3
  exact ⟨h1, h2, (Option.some.inj h3).symm⟩

theorem instSim_load8 {width : Nat} [NeZero width] {C F : Type} {p : BitVec width}
    {labs : Spt (Spt Nat)} {s1 : LabSem.State width C F} {t1 : AsmState width}
    (h : MemCtx p labs s1 t1) (r : Nat) (addr : HolAddr width)
    (hf : ¬ (asmInst (.mem .load8 r addr) s1).failed) :
    InstSim p labs (.mem .load8 r addr) s1 t1 := by
  obtain ⟨base, off⟩ := addr
  have hal := riscvByteAlignHOL_eq h.good
  simp only [asmInst, LabSem.memOp, LabSem.memLoadByte, LabSem.addrValue] at hf
  cases hb : s1.regs base with
  | loc _ _ => simp [hb, LabSem.assertState] at hf
  | word wb =>
    simp only [hb, memLoadByteAuxExact, hal] at hf
    cases hv : s1.memory (holByteAlign (wb + off)) with
    | loc _ _ => simp [hv, LabSem.assertState] at hf
    | word v =>
      by_cases hdom : s1.memDomain (holByteAlign (wb + off)) = true
      · obtain ⟨htd, -, htm⟩ := h.byte (wb + off) v hv hdom
        have htarget : AsmSem.instUpd (.mem .load8 r (.addr base off)) t1 =
            AsmSem.updReg r ((getByte (wb + off) v s1.be).setWidth width) t1 := by
          simp only [AsmSem.instUpd, AsmSem.memOp, asm_memLoad_eq, h.addr base off wb hb,
            holLOG2_one, holAligned_zero, Nat.sub_self, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
            ite_self, rmwVal, rmwOk, htd, decide_true, Bool.and_true, ← htm]
          simp [AsmSem.assertState, AsmSem.updReg, h.tfailed]
        have hsrc : asmInst (.mem .load8 r (.addr base off)) s1 =
            LabSem.updReg r (.word ((getByte (wb + off) v s1.be).setWidth width)) s1 := by
          simp [asmInst, LabSem.memOp, LabSem.memLoadByte, LabSem.addrValue, hb,
            memLoadByteAuxExact, hal, hv, hdom, getByteHOL8_eq]
        unfold InstSim
        rw [htarget, hsrc]
        refine ⟨by simp [AsmSem.updReg, h.tfailed], fun _ _ => rfl, fun r' => ?_, h.fp,
          fun x hx => (h.mem x hx).2.2⟩
        simp only [LabSem.updReg, AsmSem.updReg]
        split_ifs
        · simp [wordLocVal]
        · exact h.regs r'
      · simp [hv, hdom, LabSem.assertState] at hf

theorem instSim_store8 {width : Nat} [NeZero width] {C F : Type} {p : BitVec width}
    {labs : Spt (Spt Nat)} {s1 : LabSem.State width C F} {t1 : AsmState width}
    (h : MemCtx p labs s1 t1) (r : Nat) (addr : HolAddr width)
    (hf : ¬ (asmInst (.mem .store8 r addr) s1).failed) :
    InstSim p labs (.mem .store8 r addr) s1 t1 := by
  obtain ⟨base, off⟩ := addr
  have hal := riscvByteAlignHOL_eq h.good
  simp only [asmInst, LabSem.memOp, LabSem.memStoreByte, LabSem.addrValue] at hf
  cases hb : s1.regs base with
  | loc _ _ => simp [hb, LabSem.assertState] at hf
  | word wb =>
    simp only [hb] at hf
    cases hr : s1.regs r with
    | loc _ _ => simp [hr, LabSem.assertState] at hf
    | word w =>
      have htr : t1.regs r = w := wordLocVal_word_target (h.regs r) hr
      simp only [hr, memStoreByteAuxExact, hal] at hf
      cases hv : s1.memory (holByteAlign (wb + off)) with
      | loc _ _ => simp [hv, LabSem.assertState] at hf
      | word v =>
        by_cases hdom : s1.memDomain (holByteAlign (wb + off)) = true
        · obtain ⟨htd, hsd, -⟩ := h.byte (wb + off) v hv hdom
          have h8 : 8 ≤ width := by rcases h.good with h' | h' <;> rw [h'] <;> decide
          have htarget : AsmSem.instUpd (.mem .store8 r (.addr base off)) t1 =
              { t1 with mem := fun x => if x = (wb + off) then w.setWidth 8 else t1.mem x } := by
            simp only [AsmSem.instUpd, AsmSem.memOp, asm_memStore_eq, h.addr base off wb hb,
              holLOG2_one, holAligned_zero, Nat.sub_self,
              BitVec.add_zero, ite_self, rmwOk, htd, decide_true, Bool.and_true, wmwMem,
              AsmSem.readReg, htr]
            simp [AsmSem.assertState, h.tfailed]
          have hsrc : (asmInst (.mem .store8 r (.addr base off)) s1).memory =
              fun x => if x = holByteAlign (wb + off) then
                .word (setByte (wb + off) (w.setWidth 8) v s1.be) else s1.memory x := by
            simp [asmInst, LabSem.memOp, LabSem.memStoreByte, LabSem.addrValue, hb, hr,
              memStoreByteAuxExact, hal, hv, hdom, setByteHOL8_eq]
          have hsrcr : (asmInst (.mem .store8 r (.addr base off)) s1).regs = s1.regs := by
            simp [asmInst, LabSem.memOp, LabSem.memStoreByte, LabSem.addrValue, hb, hr,
              memStoreByteAuxExact, hal, hv, hdom]
          have hsrcf : (asmInst (.mem .store8 r (.addr base off)) s1).fpRegs = s1.fpRegs := by
            simp [asmInst, LabSem.memOp, LabSem.memStoreByte, LabSem.addrValue, hb, hr,
              memStoreByteAuxExact, hal, hv, hdom]
          unfold InstSim
          rw [htarget, hsrc, hsrcr, hsrcf]
          refine ⟨by simp [h.tfailed], fun x hx => ?_, h.regs, h.fp, fun x hx => ?_⟩
          · have : x ≠ (wb + off) := fun e => hx (e ▸ hsd)
            simp [this]
          · by_cases hxa : holByteAlign x = holByteAlign (wb + off)
            · rw [wordLocValByte, hxa, if_pos rfl]
              simp only [wordLocVal]
              by_cases hx : x = (wb + off)
              · subst hx
                simp [getByte_setByte _ _ _ _ h8]
              · rw [getByte_setByte_diff x (wb + off) _ v s1.be ⟨h.good, hx, hxa⟩]
                simp only [hx, ↓reduceIte]
                rw [← hxa] at hv hdom
                rw [(h.byte x v hv hdom).2.2]
            · have hxne : x ≠ (wb + off) := fun e => hxa (e ▸ rfl)
              rw [wordLocValByte, if_neg hxa]
              simp only [hxne, ↓reduceIte]
              exact (h.mem x hx).2.2
        · simp [hv, hdom, LabSem.assertState] at hf

/-- The addresses visited by an `n`-byte access starting from its window. -/
theorem stepAddr_window {width : Nat} [NeZero width] (be : Bool) (A : BitVec width)
    (n k : Nat) (hk : k < n) :
    stepAddr be (if be then A + BitVec.ofNat width (n - 1) else A) k =
      A + BitVec.ofNat width (if be then n - 1 - k else k) := by
  cases be
  · simp [stepAddr]
  · simp only [stepAddr, ↓reduceIte]
    have : BitVec.ofNat width (n - 1) =
        BitVec.ofNat width (n - 1 - k) + BitVec.ofNat width k := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel (by omega)]
    rw [this]; ring

/-- The four bytes of a 32-bit access at an `aligned 2` address share its
byte-aligned base and do not wrap. -/
theorem aligned2_add {width : Nat} [NeZero width] (hw : goodDimindex width)
    (A : BitVec width) (hA : holAligned 2 A = true) (m : Nat) (hm : m < 4) :
    holByteAlign (A + BitVec.ofNat width m) = holByteAlign A ∧
      (A + BitVec.ofNat width m).toNat = A.toNat + m := by
  rw [holAligned_iff] at hA
  have hx := A.isLt
  have hadd : (A + BitVec.ofNat width m).toNat = A.toNat + m := by
    rcases hw with rfl | rfl <;> rw [BitVec.toNat_add, BitVec.toNat_ofNat] <;> bv_omega
  refine ⟨?_, hadd⟩
  apply BitVec.eq_of_toNat_eq
  rw [holByteAlign_toNat hw, holByteAlign_toNat hw, hadd]
  rcases hw with rfl | rfl <;> simp only [Nat.reduceDiv] <;> omega

/-- Bits of the 32-bit word assembled from four bytes. -/
theorem getLsbD_wordOfBytes4 (be : Bool) (b0 b1 b2 b3 : BitVec 8) (j : Nat) (hj : j < 32) :
    (wordOfBytesHOL8 be (0 : BitVec 32) [b0, b1, b2, b3]).getLsbD j =
      ([b0, b1, b2, b3].getD (if be then 3 - j / 8 else j / 8) 0).getLsbD (j % 8) := by
  simp only [wordOfBytesHOL8, setByteHOL8_eq]
  have i0 : byteIndex (0 + 1 + 1 + 1 : BitVec 32) be = if be then 0 else 24 := by
    cases be <;> decide
  have i1 : byteIndex (0 + 1 + 1 : BitVec 32) be = if be then 8 else 16 := by
    cases be <;> decide
  have i2 : byteIndex (0 + 1 : BitVec 32) be = if be then 16 else 8 := by
    cases be <;> decide
  have i3 : byteIndex (0 : BitVec 32) be = if be then 24 else 0 := by
    cases be <;> decide
  repeat rw [getLsbD_setByte _ _ _ _ _ hj]
  rw [i0, i1, i2, i3]
  cases be <;> interval_cases j <;> simp

theorem holLOG2_four : holLOG2 4 = 2 := by
  rw [holLOG2_eq_log2 (by decide)]; decide

theorem instSim_load32 {width : Nat} [NeZero width] {C F : Type} {p : BitVec width}
    {labs : Spt (Spt Nat)} {s1 : LabSem.State width C F} {t1 : AsmState width}
    (h : MemCtx p labs s1 t1) (r : Nat) (addr : HolAddr width)
    (hf : ¬ (asmInst (.mem .load32 r addr) s1).failed) :
    InstSim p labs (.mem .load32 r addr) s1 t1 := by
  obtain ⟨base, off⟩ := addr
  have hal := riscvByteAlignHOL_eq h.good
  simp only [asmInst, LabSem.memOp, LabSem.memLoad32, LabSem.addrValue] at hf
  cases hb : s1.regs base with
  | loc _ _ => simp [hb, LabSem.assertState] at hf
  | word wb =>
    simp only [hb, memLoad32Exact, hal] at hf
    by_cases ha2 : holAligned 2 (wb + off) = true
    · have ha2' : riscvAlignedHOL 2 (wb + off) = true := (riscvAlignedHOL_iff 2 _).2 ha2
      cases hv : s1.memory (holByteAlign (wb + off)) with
      | loc _ _ => simp [ha2', hv, LabSem.assertState] at hf
      | word v =>
        by_cases hdom : s1.memDomain (holByteAlign (wb + off)) = true
        · -- The four bytes lie in the same source word as the access address.
          have hbytes : ∀ m < 4, t1.memDomain (wb + off + BitVec.ofNat width m) ∧
              t1.mem (wb + off + BitVec.ofNat width m) =
                getByte (wb + off + BitVec.ofNat width m) v s1.be := by
            intro m hm
            have hm' := (aligned2_add h.good _ ha2 m hm).1
            obtain ⟨h1, -, h3⟩ := h.byte _ v (by rw [hm']; exact hv) (by rw [hm']; exact hdom)
            exact ⟨h1, h3⟩
          have hok : rmwOk t1.be t1.memDomain (if t1.be then wb + off + BitVec.ofNat width (4 - 1)
              else wb + off) 4 = true := by
            rw [rmwOk_iff]
            intro k hk
            rw [stepAddr_window t1.be _ 4 k hk]
            exact (hbytes _ (by split <;> omega)).1
          have hval : rmwVal (rw := width) t1.be t1.mem (if t1.be then wb + off +
              BitVec.ofNat width (4 - 1) else wb + off) 4 =
              (wordOfBytesHOL8 s1.be (0 : BitVec 32)
                [getByteHOL8 (wb + off) v s1.be, getByteHOL8 (wb + off + 1) v s1.be,
                  getByteHOL8 (wb + off + 2) v s1.be,
                  getByteHOL8 (wb + off + 3) v s1.be]).setWidth width := by
            apply BitVec.eq_of_getLsbD_eq
            intro j hj
            rw [getLsbD_rmwVal _ _ _ _ _ (goodDimindex_four_le h.good) hj,
              BitVec.getLsbD_setWidth]
            by_cases hj32 : j < 32
            · rw [getLsbD_wordOfBytes4 _ _ _ _ _ _ hj32, ← h.be]
              have hlt : j / 8 < 4 := by omega
              rw [decide_eq_true hlt, Bool.true_and, stepAddr_window _ _ 4 _ hlt]
              have hk : (if s1.be then 4 - 1 - j / 8 else j / 8) < 4 := by split <;> omega
              rw [(hbytes _ hk).2, getLsbD_getByte _ _ _ _ (Nat.mod_lt _ (by decide))]
              simp only [getByteHOL8_eq]
              rcases (show j / 8 = 0 ∨ j / 8 = 1 ∨ j / 8 = 2 ∨ j / 8 = 3 by omega) with
                e | e | e | e <;> cases hbe : s1.be <;> simp [e, hj, getLsbD_getByte _ _ _ _
                  (Nat.mod_lt _ (by decide : 0 < 8))]
            · have hlt : ¬ j / 8 < 4 := by omega
              simp only [hlt, decide_false, Bool.false_and, hj, decide_true,
                Bool.true_and]
              exact (BitVec.getLsbD_of_ge _ _ (by omega)).symm
          have htarget : AsmSem.instUpd (.mem .load32 r (.addr base off)) t1 =
              AsmSem.updReg r ((wordOfBytesHOL8 s1.be (0 : BitVec 32)
                [getByteHOL8 (wb + off) v s1.be, getByteHOL8 (wb + off + 1) v s1.be,
                  getByteHOL8 (wb + off + 2) v s1.be,
                  getByteHOL8 (wb + off + 3) v s1.be]).setWidth width) t1 := by
            simp only [AsmSem.instUpd, AsmSem.memOp, asm_memLoad_eq, h.addr base off wb hb,
              holLOG2_four, ha2, hok, hval]
            simp [AsmSem.assertState, AsmSem.updReg, h.tfailed]
          have hsrc : asmInst (.mem .load32 r (.addr base off)) s1 =
              LabSem.updReg r (.word ((wordOfBytesHOL8 s1.be (0 : BitVec 32)
                [getByteHOL8 (wb + off) v s1.be, getByteHOL8 (wb + off + 1) v s1.be,
                  getByteHOL8 (wb + off + 2) v s1.be,
                  getByteHOL8 (wb + off + 3) v s1.be]).setWidth width)) s1 := by
            simp [asmInst, LabSem.memOp, LabSem.memLoad32, LabSem.addrValue, hb,
              memLoad32Exact, hal, ha2', hv, hdom]
          unfold InstSim
          rw [htarget, hsrc]
          refine ⟨by simp [AsmSem.updReg, h.tfailed], fun _ _ => rfl, fun r' => ?_, h.fp,
            fun x hx => (h.mem x hx).2.2⟩
          simp only [LabSem.updReg, AsmSem.updReg]
          split_ifs
          · simp [wordLocVal]
          · exact h.regs r'
        · simp [ha2', hv, hdom, LabSem.assertState] at hf
    · have : riscvAlignedHOL 2 (wb + off) = false := by
        cases e : riscvAlignedHOL 2 (wb + off)
        · rfl
        · exact absurd ((riscvAlignedHOL_iff 2 _).1 e) ha2
      simp [this, LabSem.assertState] at hf

/-- The offsets `A + m` (as literals) of a 32-bit access. -/
theorem aligned2_lit {width : Nat} [NeZero width] (hw : goodDimindex width)
    (A : BitVec width) (hA : holAligned 2 A = true) :
    holByteAlign (A + 1) = holByteAlign A ∧ holByteAlign (A + 2) = holByteAlign A ∧
    holByteAlign (A + 3) = holByteAlign A ∧
    A ≠ A + 1 ∧ A ≠ A + 2 ∧ A ≠ A + 3 ∧ A + 1 ≠ A + 2 ∧ A + 1 ≠ A + 3 ∧ A + 2 ≠ A + 3 := by
  have e1 := aligned2_add hw A hA 1 (by decide)
  have e2 := aligned2_add hw A hA 2 (by decide)
  have e3 := aligned2_add hw A hA 3 (by decide)
  simp only [show BitVec.ofNat width 1 = 1 from rfl, show BitVec.ofNat width 2 = 2 from rfl,
    show BitVec.ofNat width 3 = 3 from rfl] at e1 e2 e3
  refine ⟨e1.1, e2.1, e3.1, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;>
    have := congrArg BitVec.toNat heq <;> simp only [e1.2, e2.2, e3.2] at this <;> omega

/-- Every byte of the word after the four byte writes of a 32-bit store. -/
theorem getByte_store32 {width : Nat} [NeZero width] (hw : goodDimindex width)
    (A v : BitVec width) (hA : holAligned 2 A = true) (b0 b1 b2 b3 : BitVec 8) (be : Bool)
    (x : BitVec width) (hx : holByteAlign x = holByteAlign A) :
    getByte x (setByte (A + 3) b3 (setByte (A + 2) b2 (setByte (A + 1) b1
        (setByte A b0 v be) be) be) be) be =
      if x = A then b0 else if x = A + 1 then b1 else if x = A + 2 then b2
      else if x = A + 3 then b3 else getByte x v be := by
  have h8 : 8 ≤ width := by rcases hw with rfl | rfl <;> decide
  obtain ⟨a1, a2, a3, d01, d02, d03, d12, d13, d23⟩ := aligned2_lit hw A hA
  have diff : ∀ y z (b : BitVec 8) (u : BitVec width), y ≠ z →
      holByteAlign y = holByteAlign z → getByte y (setByte z b u be) be = getByte y u be :=
    fun y z b u hne hal => getByte_setByte_diff y z b u be ⟨hw, hne, hal⟩
  by_cases h3 : x = A + 3
  · subst h3
    rw [getByte_setByte _ _ _ _ h8, if_neg d03.symm, if_neg d13.symm, if_neg d23.symm,
      if_pos rfl]
  rw [diff _ _ _ _ h3 (by rw [hx, a3])]
  by_cases h2 : x = A + 2
  · subst h2
    rw [getByte_setByte _ _ _ _ h8, if_neg d02.symm, if_neg d12.symm, if_pos rfl]
  rw [diff _ _ _ _ h2 (by rw [hx, a2])]
  by_cases h1 : x = A + 1
  · subst h1
    rw [getByte_setByte _ _ _ _ h8, if_neg d01.symm, if_pos rfl]
  rw [diff _ _ _ _ h1 (by rw [hx, a1])]
  by_cases h0 : x = A
  · subst h0
    rw [getByte_setByte _ _ _ _ h8, if_pos rfl]
  rw [diff _ _ _ _ h0 hx, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

/-- The `m`-th byte of the low 32 bits of a register, as the 32-bit store
extracts it. -/
theorem getByte32_setWidth {width : Nat} [NeZero width] (w : BitVec width)
    (be : Bool) (m : Nat) (hm : m < 4) :
    getByte (BitVec.ofNat 32 m) (w.setWidth 32) be =
      (w >>> (8 * (if be then 4 - 1 - m else m))).setWidth 8 := by
  have hidx : byteIndex (BitVec.ofNat 32 m) be = if be then 8 * (3 - m) else 8 * m := by
    have : (BitVec.ofNat 32 m).toNat % 4 = m := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show m < 2 ^ 32 by omega),
        Nat.mod_eq_of_lt hm]
    cases be <;> simp only [byteIndex, this, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_getByte _ _ _ _ hi, hidx]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true,
    Bool.true_and]
  cases be <;> simp <;> omega

theorem instSim_store32 {width : Nat} [NeZero width] {C F : Type} {p : BitVec width}
    {labs : Spt (Spt Nat)} {s1 : LabSem.State width C F} {t1 : AsmState width}
    (h : MemCtx p labs s1 t1) (r : Nat) (addr : HolAddr width)
    (hf : ¬ (asmInst (.mem .store32 r addr) s1).failed) :
    InstSim p labs (.mem .store32 r addr) s1 t1 := by
  obtain ⟨base, off⟩ := addr
  have hal := riscvByteAlignHOL_eq h.good
  simp only [asmInst, LabSem.memOp, LabSem.memStore32, LabSem.addrValue] at hf
  cases hb : s1.regs base with
  | loc _ _ => simp [hb, LabSem.assertState] at hf
  | word wb =>
    simp only [hb] at hf
    cases hr : s1.regs r with
    | loc _ _ => simp [hr, LabSem.assertState] at hf
    | word w =>
      have htr : t1.regs r = w := wordLocVal_word_target (h.regs r) hr
      simp only [hr, memStore32Exact, hal] at hf
      by_cases ha2 : holAligned 2 (wb + off) = true
      · have ha2' : riscvAlignedHOL 2 (wb + off) = true := (riscvAlignedHOL_iff 2 _).2 ha2
        cases hv : s1.memory (holByteAlign (wb + off)) with
        | loc _ _ => simp [ha2', hv, LabSem.assertState] at hf
        | word v =>
          by_cases hdom : s1.memDomain (holByteAlign (wb + off)) = true
          · obtain ⟨a1, a2, a3, d01, d02, d03, d12, d13, d23⟩ := aligned2_lit h.good _ ha2
            have hbytes : ∀ m < 4, t1.memDomain (wb + off + BitVec.ofNat width m) ∧
                s1.memDomain (wb + off + BitVec.ofNat width m) = true := by
              intro m hm
              have hm' := (aligned2_add h.good _ ha2 m hm).1
              obtain ⟨h1, h2, -⟩ :=
                h.byte _ v (by rw [hm']; exact hv) (by rw [hm']; exact hdom)
              exact ⟨h1, h2⟩
            have hok : rmwOk t1.be t1.memDomain (if t1.be then wb + off +
                BitVec.ofNat width (4 - 1) else wb + off) 4 = true := by
              rw [rmwOk_iff]
              intro k hk
              rw [stepAddr_window t1.be _ 4 k hk]
              exact (hbytes _ (by split <;> omega)).1
            have h4 : 4 ≤ 2 ^ width :=
              le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide)
                (le_trans (by decide) (goodDimindex_four_le h.good)))
            have hwin : ∀ m < 4, wmwMem t1.be t1.mem (if t1.be then wb + off +
                BitVec.ofNat width (4 - 1) else wb + off) 4 w (wb + off + BitVec.ofNat width m) =
                getByte (BitVec.ofNat 32 m) (w.setWidth 32) s1.be := by
              intro m hm
              have hk : (if t1.be then 4 - 1 - m else m) < 4 := by split <;> omega
              have hs := stepAddr_window t1.be (wb + off) 4 _ hk
              rw [show (if t1.be then 4 - 1 - (if t1.be then 4 - 1 - m else m) else
                  (if t1.be then 4 - 1 - m else m)) = m by cases t1.be <;> first | (simp; done) | (simp; omega)] at hs
              conv_lhs => rw [← hs]
              rw [wmwMem_step _ _ _ _ _ _ (goodDimindex_four_le h.good) hk h4,
                getByte32_setWidth w s1.be m hm, h.be]
            have hwout : ∀ x, (∀ m < 4, x ≠ wb + off + BitVec.ofNat width m) →
                wmwMem t1.be t1.mem (if t1.be then wb + off + BitVec.ofNat width (4 - 1)
                  else wb + off) 4 w x = t1.mem x := by
              intro x hx
              apply wmwMem_other
              intro k hk
              rw [stepAddr_window _ _ 4 k hk]
              exact hx _ (by split <;> omega)
            have htarget : AsmSem.instUpd (.mem .store32 r (.addr base off)) t1 =
                { t1 with mem := wmwMem t1.be t1.mem (if t1.be then wb + off +
                  BitVec.ofNat width (4 - 1) else wb + off) 4 w } := by
              simp only [AsmSem.instUpd, AsmSem.memOp, asm_memStore_eq, h.addr base off wb hb,
                holLOG2_four, ha2, hok, AsmSem.readReg, htr]
              simp [AsmSem.assertState, h.tfailed]
            have hsrc : (asmInst (.mem .store32 r (.addr base off)) s1).memory =
                fun x => if x = holByteAlign (wb + off) then
                  .word (setByte (wb + off + 3)
                    (getByte (3 : BitVec 32) (w.setWidth 32) s1.be)
                    (setByte (wb + off + 2) (getByte (2 : BitVec 32) (w.setWidth 32) s1.be)
                      (setByte (wb + off + 1) (getByte (1 : BitVec 32) (w.setWidth 32) s1.be)
                        (setByte (wb + off) (getByte (0 : BitVec 32) (w.setWidth 32) s1.be)
                          v s1.be) s1.be) s1.be) s1.be)
                  else s1.memory x := by
              simp [asmInst, LabSem.memOp, LabSem.memStore32, LabSem.addrValue, hb, hr,
                memStore32Exact, hal, ha2', hv, hdom, setByteHOL8_eq, getByteHOL8_eq]
            have hsrcr : (asmInst (.mem .store32 r (.addr base off)) s1).regs = s1.regs := by
              simp [asmInst, LabSem.memOp, LabSem.memStore32, LabSem.addrValue, hb, hr,
                memStore32Exact, hal, ha2', hv, hdom]
            have hsrcf : (asmInst (.mem .store32 r (.addr base off)) s1).fpRegs = s1.fpRegs := by
              simp [asmInst, LabSem.memOp, LabSem.memStore32, LabSem.addrValue, hb, hr,
                memStore32Exact, hal, ha2', hv, hdom]
            -- The four written addresses in literal form.
            have l0 : wb + off + BitVec.ofNat width 0 = wb + off := by simp
            have l1 : wb + off + BitVec.ofNat width 1 = wb + off + 1 := rfl
            have l2 : wb + off + BitVec.ofNat width 2 = wb + off + 2 := rfl
            have l3 : wb + off + BitVec.ofNat width 3 = wb + off + 3 := rfl
            unfold InstSim
            rw [htarget, hsrc, hsrcr, hsrcf]
            refine ⟨by simp [h.tfailed], fun x hx => ?_, h.regs, h.fp, fun x hx => ?_⟩
            · apply hwout
              intro m hm heq
              exact hx (heq ▸ (hbytes m hm).2)
            · by_cases hxa : holByteAlign x = holByteAlign (wb + off)
              · rw [wordLocValByte, hxa, if_pos rfl]
                simp only [wordLocVal]
                rw [getByte_store32 h.good _ v ha2 _ _ _ _ s1.be x hxa]
                have w0 := hwin 0 (by decide)
                have w1 := hwin 1 (by decide)
                have w2 := hwin 2 (by decide)
                rw [l0] at w0
                rw [l1] at w1
                rw [l2] at w2
                by_cases e0 : x = wb + off
                · rw [if_pos e0, e0, w0]; rfl
                by_cases e1 : x = wb + off + 1
                · rw [if_neg e0, if_pos e1, e1, w1]; rfl
                by_cases e2 : x = wb + off + 2
                · rw [if_neg e0, if_neg e1, if_pos e2, e2, w2]; rfl
                by_cases e3 : x = wb + off + 3
                · rw [if_neg e0, if_neg e1, if_neg e2, if_pos e3, e3]
                  exact (congrArg some (hwin 3 (by decide))).symm
                rw [if_neg e0, if_neg e1, if_neg e2, if_neg e3]
                rw [hwout x (by
                  intro m hm heq
                  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 by omega) with
                    rfl | rfl | rfl | rfl
                  · exact e0 (heq.trans l0)
                  · exact e1 heq
                  · exact e2 heq
                  · exact e3 heq)]
                rw [← hxa] at hv hdom
                rw [(h.byte x v hv hdom).2.2]
              · rw [wordLocValByte, if_neg hxa]
                simp only
                rw [hwout x (by
                  intro m hm heq
                  apply hxa
                  rw [heq, (aligned2_add h.good _ ha2 m hm).1])]
                exact (h.mem x hx).2.2
          · simp [ha2', hv, hdom, LabSem.assertState] at hf
      · have : riscvAlignedHOL 2 (wb + off) = false := by
          cases e : riscvAlignedHOL 2 (wb + off)
          · rfl
          · exact absurd ((riscvAlignedHOL_iff 2 _).1 e) ha2
        simp [this, LabSem.assertState] at hf

/-- Every memory instruction: ordinary 16-bit accesses always fail in the
source, so only the remaining six operations need a simulation. -/
theorem instSim_mem {width : Nat} [NeZero width] {C F : Type} {p : BitVec width}
    {labs : Spt (Spt Nat)} {s1 : LabSem.State width C F} {t1 : AsmState width}
    (h : MemCtx p labs s1 t1) (m : HolMemop) (r : Nat) (addr : HolAddr width)
    (hf : ¬ (asmInst (.mem m r addr) s1).failed) :
    InstSim p labs (.mem m r addr) s1 t1 := by
  cases m with
  | load => exact instSim_load h r addr hf
  | store => exact instSim_store h r addr hf
  | load8 => exact instSim_load8 h r addr hf
  | store8 => exact instSim_store8 h r addr hf
  | load32 => exact instSim_load32 h r addr hf
  | store32 => exact instSim_store32 h r addr hf
  | load16 => exact absurd (by simp [asmInst, LabSem.memOp, LabSem.assertState]) hf
  | store16 => exact absurd (by simp [asmInst, LabSem.memOp, LabSem.assertState]) hf

end Flapjack.Compiler.Backend.LabToTarget
