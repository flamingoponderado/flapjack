import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Misc.Alignment
import Flapjack.Misc.GoodDimindex
import Flapjack.Misc.Fun2SetUnion
import Flapjack.Compiler.Backend.LabToTarget.Initialization
import Flapjack.Compiler.Backend.StackToLab.Proofs.MakeInit

/-!
# `pan_to_target_compile_semantics` assembly, stage A3b arithmetic

The address-range fact inside the `memory_assumption` step of the HOL proof of
`pan_to_target_compile_semantics` (`pan_to_targetProofScript.sml:1499-1545`): under
`good_dimindex`, the byte-aligned words of the interval `[a, b)` between two aligned
bounds are exactly `addresses a (w2n (-1w * a + b) DIV (dimindex DIV 8))`, and that
many words fit in the address space. Intermediate steps of the single HOL proof, so
untagged.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Backend

/-- Under `good_dimindex`, `byte_aligned` is divisibility by the word size in bytes
(Flapjack infrastructure; HOL's `aligned_w2n` with `2 ** LOG2 (dimindex DIV 8)`). -/
theorem holByteAligned_iff_mod {width : Nat} [NeZero width] (good : goodDimindex width)
    (x : BitVec width) : holByteAligned x = true ↔ x.toNat % (width / 8) = 0 := by
  have hp : 2 ^ holLOG2 (width / 8) = width / 8 := by
    rcases good with h | h <;> subst h
    · rw [holLOG2_eq_log2 (by decide)]; decide
    · rw [holLOG2_eq_log2 (by decide)]; decide
  unfold holByteAligned
  rw [holAligned_iff, hp]

/-- `bytes_in_word` is the word size in bytes under `good_dimindex` (Flapjack
infrastructure). -/
theorem bytesInWord_toNat {width : Nat} [NeZero width] (good : goodDimindex width) :
    (StackRemove.bytesInWord width).toNat = width / 8 := by
  rcases good with h | h <;> subst h <;> rfl

/-- The byte-aligned words of `[a, b)` are the `addresses` range from `a`
(HOL proof lines 1513-1545, via `addresses_thm`, `aligned_w2n`, `DIVISION`,
`DIV_LESS_DIV`, `MOD_SUB_LEMMA` and `word_arith_lemma2`). -/
theorem alignedInterval_eq_addresses {width : Nat} [NeZero width] (good : goodDimindex width)
    (a b : BitVec width) (ha : holByteAligned a = true) (hb : holByteAligned b = true)
    (hab : a ≤ b) :
    (fun x => holByteAligned x = true ∧ a ≤ x ∧ x < b) =
      StackRemove.addresses a ((-1 * a + b).toNat / (width / 8)) := by
  have hd : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
  have hdw : width / 8 < 2 ^ width := by rcases good with h | h <;> subst h <;> decide
  rw [holByteAligned_iff_mod good] at ha hb
  have hab' : a.toNat ≤ b.toNat := hab
  have hdiff : (-1 * a + b).toNat = b.toNat - a.toNat := by
    have : -1 * a + b = b - a := by
      rw [show (-1 : BitVec width) * a = -a by simp, BitVec.add_comm, ← BitVec.sub_eq_add_neg]
    rw [this, BitVec.toNat_sub_of_le hab]
  have hbw := b.isLt
  funext x
  apply propext
  rw [StackRemove.mem_addresses, holByteAligned_iff_mod good, hdiff]
  constructor
  · rintro ⟨hx, hax, hxb⟩
    have hax' : a.toNat ≤ x.toNat := hax
    have hxb' : x.toNat < b.toNat := hxb
    refine ⟨(x.toNat - a.toNat) / (width / 8), ?_, ?_⟩
    · have h1 : (width / 8) ∣ (x.toNat - a.toNat) := Nat.dvd_sub (Nat.dvd_of_mod_eq_zero hx)
        (Nat.dvd_of_mod_eq_zero ha)
      have h2 : (width / 8) ∣ (b.toNat - a.toNat) := Nat.dvd_sub (Nat.dvd_of_mod_eq_zero hb)
        (Nat.dvd_of_mod_eq_zero ha)
      obtain ⟨i, hi⟩ := h1
      obtain ⟨j, hj⟩ := h2
      rw [hi, hj, Nat.mul_div_cancel_left _ hd, Nat.mul_div_cancel_left _ hd]
      have : (width / 8) * i < (width / 8) * j := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    · apply BitVec.eq_of_toNat_eq
      have h1 : (width / 8) ∣ (x.toNat - a.toNat) := Nat.dvd_sub (Nat.dvd_of_mod_eq_zero hx)
        (Nat.dvd_of_mod_eq_zero ha)
      have hmul : (x.toNat - a.toNat) / (width / 8) * (width / 8) = x.toNat - a.toNat :=
        Nat.div_mul_cancel h1
      have hlt : (x.toNat - a.toNat) / (width / 8) < 2 ^ width := by
        have := Nat.div_le_self (x.toNat - a.toNat) (width / 8)
        have := x.isLt
        omega
      have hxlt := x.isLt
      have e1 : (x.toNat - a.toNat) / (width / 8) % 2 ^ width = (x.toNat - a.toNat) / (width / 8) :=
        Nat.mod_eq_of_lt hlt
      have e2 : (x.toNat - a.toNat) / (width / 8) * (width / 8) % 2 ^ width = x.toNat - a.toNat := by
        rw [hmul]; exact Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, bytesInWord_toNat good, e1, e2,
        Nat.mod_eq_of_lt (by omega)]
      omega
  · rintro ⟨i, hi, rfl⟩
    have hle := (Nat.le_div_iff_mul_le hd).mp hi
    rw [Nat.succ_mul] at hle
    have hilt : i * (width / 8) < b.toNat - a.toNat := by omega
    have hi2 : i < 2 ^ width := by
      have : i ≤ i * (width / 8) := Nat.le_mul_of_pos_right i hd
      omega
    have hval : (a + BitVec.ofNat width i * StackRemove.bytesInWord width).toNat =
        a.toNat + i * (width / 8) := by
      rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, bytesInWord_toNat good,
        Nat.mod_eq_of_lt hi2, Nat.mod_eq_of_lt (show i * (width / 8) < 2 ^ width by omega),
        Nat.mod_eq_of_lt (show a.toNat + i * (width / 8) < 2 ^ width by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hval, Nat.add_mul_mod_self_right]; exact ha
    · show a.toNat ≤ _
      rw [hval]; omega
    · show _ < b.toNat
      rw [hval]; omega

/-- Stage A3b of the HOL proof (lines 1486-1550): the `memory_assumption` of
`full_make_init_semantics` for the initial lab state, from the `pan_installed`
components (heap/stack range between the two heap registers, the bitmap region and
its separation, and the five configuration words). -/
theorem panToTargetMemoryAssumption {width : Nat} [NeZero width] {S Q F C : Type}
    (good : goodDimindex width) (regNames : Spt Nat) (mc : MachineConfig width S Q)
    (ffi : HolFfiState F) (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapPtr : BitVec width) (bitmapsDm sdm' : BitVec width → Bool) (ms : S)
    (code : LabSem.LabProgHOL width)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (bytes : List (BitVec 8)) (cbspace : Nat) (coracle : Nat → C × LabSem.LabProgHOL width)
    (bitmaps : List (BitVec width)) (dataSp : Nat) :
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let biw := StackRemove.bytesInWord width
    let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    holByteAligned (t.regs r1) = true ∧ holByteAligned (t.regs r2) = true ∧
    holByteAligned bitmapPtr = true ∧ t.regs r1 ≤ t.regs r2 ∧
    1024 * biw ≤ t.regs r2 - t.regs r1 ∧
    (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
    m (t.regs r1) = .word bitmapPtr ∧
    m (t.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) ∧
    m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width dataSp +
      biw * BitVec.ofNat width bitmaps.length) ∧
    m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
    m (t.regs r1 + 4 * biw) =
      .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
    SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
      (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) dataSp)
      (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)) →
    StackToLab.Proofs.MakeInit.memoryAssumption regNames bitmaps dataSp
      (LabToTarget.makeInit (C := C) mc ffi t m
        (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a) sdm' ms code comp
        (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle) := by
  intro r1 r2 biw heapStackDm
  rintro ⟨ha1, ha2, hbp, hle, hsize, hdisj, hm0, hm1, hm2, hm3, hm4, hstar⟩
  have hdw : (-1 * t.regs r1 + t.regs r2).toNat / (width / 8) * (width / 8) < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) (BitVec.isLt _)
  refine ⟨t.regs r1, t.regs (StackNames.findNameSpt regNames 3), t.regs r2, bitmapPtr,
    rfl, rfl, rfl, hm0, hm1, hm2, hm3, ?_, rfl, hle, ha1, ha2, hbp, hsize, ?_⟩
  · simp only [LabToTarget.makeInit]
    rw [hm4]
    congr 1
    ac_rfl
  · simp only [LabToTarget.makeInit, bytesInWord_toNat good]
    have hset : (fun a => ((heapStackDm a || bitmapsDm a) && holByteAligned a) = true) =
        (fun a => (holByteAligned a = true ∧ bitmapsDm a = true) ∨
          (holByteAligned a = true ∧ t.regs r1 ≤ a ∧ a < t.regs r2)) := by
      funext a
      apply propext
      simp only [heapStackDm, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      tauto
    rw [hset]
    apply Misc.Fun2SetUnion.fun2SetDisjointUnion
    refine ⟨?_, hstar, ?_⟩
    · intro x ⟨⟨_, hb⟩, _, hh⟩
      exact hdisj x ⟨by simp [heapStackDm, hh], hb⟩
    · rw [alignedInterval_eq_addresses good _ _ ha1 ha2 hle]
      exact BackendProof.wordListExistsImp _ _ _ _ ⟨rfl, by rw [Nat.mul_comm]; exact hdw, good⟩

end Flapjack.Pancake.Proofs.PanToTarget
