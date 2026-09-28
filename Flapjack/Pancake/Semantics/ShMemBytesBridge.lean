import Flapjack.Pancake.Semantics.PanSem.ShMemExact
import Flapjack.Pancake.Semantics.CrepSem.TotalEval
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

/-!
# Byte-list bridge between the exact Pan and Crep shared-memory primitives

The exact Pan `shMemLoadHOLExact`/`shMemStoreHOLExact`
(`Flapjack/Pancake/Semantics/PanSem/ShMemExact.lean`) hand the FFI the
little-endian byte encoding `panWordToBytesHOL w false`, while the exact Crep
`crepShMemLoadExactHOL`/`crepShMemStoreExactHOL`
(`Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean`) hand it
`(crepClockWordToBytes w).map UInt8.toBitVec`.  This file proves these two byte
lists are equal for every positive width, so the two primitives issue the same
`call_FFI` request whenever their FFI states and domains agree, and derives the
result correspondence of the two primitives: the same `.finalFfi` oracle event,
the same `.error`, or the same successful `none` (the `.ret` FFI-return case).

This is Flapjack-specific bridge infrastructure for the `pc_compile_correct`
ShMemLoad/ShMemStore cases; it has no standalone HOL declaration and therefore
no `@[hol]` tag.  The remaining obligations of that bridge are still tracked by
`flapjack-pxn.18.4.3.111.1`: the decoded `word_of_bytes` equality (the value
installed on a `.ret`) and the `locals_rel` slot maintenance of the written
variable.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS)

/-- The little-endian byte encodings used by the exact Pan and Crep
    shared-memory primitives coincide: `panWordToBytesHOL w false` (index
    `i` is HOL `get_byte` at address `i`, little-endian) equals
    `(crepClockWordToBytes w).map UInt8.toBitVec` (index `i` is
    `(w.toNat / 256 ^ i) % 256`). -/
theorem panWordToBytesHOL_eq_map_crepClockWordToBytes {width : Nat} [NeZero width]
    (value : RiscV.Word width) :
    panWordToBytesHOL value false = (crepClockWordToBytes value).map UInt8.toBitVec := by
  unfold panWordToBytesHOL crepClockWordToBytes
  rw [List.map_map]
  apply List.map_congr_left
  intro index hindex
  simp only [Function.comp_apply]
  have hidxlt : index < width / 8 := List.mem_range.mp hindex
  have htoNat : (BitVec.ofNat width index).toNat = index := by
    have h2 : width < 2 ^ width := Nat.lt_two_pow_self
    have h1 : width / 8 ≤ width := Nat.div_le_self _ _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hidx : (BitVec.ofNat width index).toNat % (width / 8) = index := by
    rw [htoNat, Nat.mod_eq_of_lt hidxlt]
  have hexp : 256 ^ index = 2 ^ (8 * index) := by
    rw [show (256 : Nat) = 2 ^ 8 by decide]
    rw [← Nat.pow_mul]
  simp only [panGetByteHOL, Bool.false_eq_true, if_false, hidx,
    UInt8.toNat_ofNat', Nat.mod_mod]
  rw [hexp, UInt8.toBitVec_ofNat']

/-- The Pan shared-memory load issues the same `call_FFI` request as the exact
    Crep shared-memory load: for equal FFI states, byte count and address the
    (mapped-read) oracle receives identical byte lists. -/
theorem callFFIHOL_sharedMemRead_eq {width : Nat} [NeZero width] {σ : Type}
    (ffi : HolFfiState σ) (nb : Nat) (address : RiscV.Word width) :
    callFFIHOL ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
        (panWordToBytesHOL address false) =
      callFFIHOL ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
        ((crepClockWordToBytes address).map UInt8.toBitVec) := by
  rw [panWordToBytesHOL_eq_map_crepClockWordToBytes]

/-- The Pan shared-memory store issues the same `call_FFI` request as the exact
    Crep shared-memory store for the whole-word (`nb = 0`) encoding: for equal
    FFI states the (mapped-write) oracle receives identical byte lists. -/
theorem callFFIHOL_sharedMemWrite_eq {width : Nat} [NeZero width] {σ : Type}
    (ffi : HolFfiState σ) (nb : Nat) (value address : RiscV.Word width) :
    callFFIHOL ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
        (panWordToBytesHOL value false ++ panWordToBytesHOL address false) =
      callFFIHOL ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
        ((crepClockWordToBytes value ++ crepClockWordToBytes address).map
          UInt8.toBitVec) := by
  rw [panWordToBytesHOL_eq_map_crepClockWordToBytes value,
    panWordToBytesHOL_eq_map_crepClockWordToBytes address, List.map_append]

/-- The Pan shared-memory store's byte-aligned-prefix (`nb ≠ 0`) request also
    agrees with the exact Crep request: the `TAKE nb` prefix is mapped through
    the same byte encoding. -/
theorem callFFIHOL_sharedMemWrite_take_eq {width : Nat} [NeZero width] {σ : Type}
    (ffi : HolFfiState σ) (nb : Nat) (value address : RiscV.Word width) :
    callFFIHOL ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
        ((panWordToBytesHOL value false).take nb ++ panWordToBytesHOL address false) =
      callFFIHOL ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
        (((crepClockWordToBytes value).take nb ++ crepClockWordToBytes address).map
          UInt8.toBitVec) := by
  rw [panWordToBytesHOL_eq_map_crepClockWordToBytes value,
    panWordToBytesHOL_eq_map_crepClockWordToBytes address, List.map_append,
    ← List.map_take]

/-- Result correspondence of the exact Pan and Crep shared-memory loads: for
    equal FFI states and domains the two primitives agree on the FFI oracle
    event (`some (.finalFfi e)`), on `.error`, or on the successful `none`
    (FFI-returned) case.  The `.ret` branch leaves the decoded value and the
    written variable for the `locals_rel` slot obligation (see the module
    docstring). -/
theorem shMemLoadHOLExact_control_corresponds {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateExact width σ) [DecidablePred source.shMemaddrs]
    (target : CrepSemHOLState width σ) [DecidablePred target.shMemaddrs]
    (kind : VarKind) (name : MlS) (crepName : Nat) (address : RiscV.Word width) (nb : Nat)
    (hffi : source.ffi = target.ffi)
    (hdom : ∀ a, source.shMemaddrs a = target.shMemaddrs a) :
    (∃ e : HolFinalEvent, (shMemLoadHOLExact source kind name address nb).1 = some (.finalFfi e) ∧
        (crepShMemLoadExactHOL crepName address nb target).1 = some (.finalFfi e)) ∨
      ((shMemLoadHOLExact source kind name address nb).1 = some .error ∧
        (crepShMemLoadExactHOL crepName address nb target).1 = some .error) ∨
      ((shMemLoadHOLExact source kind name address nb).1 = none ∧
        (crepShMemLoadExactHOL crepName address nb target).1 = none) := by
  unfold shMemLoadHOLExact crepShMemLoadExactHOL
  rw [hffi, panWordToBytesHOL_eq_map_crepClockWordToBytes address]
  simp only [hdom]
  split
  · split
    · cases hcall : callFFIHOL target.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          ((crepClockWordToBytes address).map UInt8.toBitVec) with
      | final event => exact Or.inl ⟨event, rfl, rfl⟩
      | ret newFfi newBytes => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · split
    · cases hcall : callFFIHOL target.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          ((crepClockWordToBytes address).map UInt8.toBitVec) with
      | final event => exact Or.inl ⟨event, rfl, rfl⟩
      | ret newFfi newBytes => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- Result correspondence of the exact Pan and Crep shared-memory stores: for
    equal FFI states and domains, and a target local holding the stored word,
    the two primitives agree on the FFI oracle event, on `.error`, or on the
    successful `none` case. -/
theorem shMemStoreHOLExact_control_corresponds {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateExact width σ) [DecidablePred source.shMemaddrs]
    (target : CrepSemHOLState width σ) [DecidablePred target.shMemaddrs]
    (word : RiscV.Word width) (crepName : Nat) (address : RiscV.Word width) (nb : Nat)
    (hffi : source.ffi = target.ffi)
    (hdom : ∀ a, source.shMemaddrs a = target.shMemaddrs a)
    (hlocal : target.locals.lookup crepName = some (.word word)) :
    (∃ e : HolFinalEvent, (shMemStoreHOLExact source word address nb).1 = some (.finalFfi e) ∧
        (crepShMemStoreExactHOL crepName address nb target).1 = some (.finalFfi e)) ∨
      ((shMemStoreHOLExact source word address nb).1 = some .error ∧
        (crepShMemStoreExactHOL crepName address nb target).1 = some .error) ∨
      ((shMemStoreHOLExact source word address nb).1 = none ∧
        (crepShMemStoreExactHOL crepName address nb target).1 = none) := by
  unfold shMemStoreHOLExact crepShMemStoreExactHOL
  simp only [hlocal]
  rw [hffi, panWordToBytesHOL_eq_map_crepClockWordToBytes word,
    panWordToBytesHOL_eq_map_crepClockWordToBytes address]
  simp only [List.map_append, ← List.map_take]
  simp only [hdom]
  split
  · split
    · cases hcall : callFFIHOL target.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
          (List.map UInt8.toBitVec (crepClockWordToBytes word) ++
            List.map UInt8.toBitVec (crepClockWordToBytes address)) with
      | final event => exact Or.inl ⟨event, rfl, rfl⟩
      | ret newFfi newBytes => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · split
    · cases hcall : callFFIHOL target.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
          (List.map UInt8.toBitVec (List.take nb (crepClockWordToBytes word)) ++
            List.map UInt8.toBitVec (crepClockWordToBytes address)) with
      | final event => exact Or.inl ⟨event, rfl, rfl⟩
      | ret newFfi newBytes => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-! ## Decoded-word arithmetic for the shared-memory byte lists

The `shMemLoad` case of `pc_compile_correct` must also match the word that the
FFI hands back.  The Crep primitive decodes `newBytes.map UInt8.ofBitVec` with
`crepClockWordOfBytes`, while the Pan primitive decodes `newBytes` with
`panWordOfBytesHOL false 0`.  This section develops the byte-sum arithmetic
shared by both decoders: both equal the little-endian integer sum
`∑ b_i * 256 ^ i` reduced modulo `2 ^ width`, so the two decoders agree for
every byte list when `8 ∣ width` (the convention of the existing byte carriers:
`panWordToBytesHOL`/`panSetByteHOL` already index `width / 8` byte slots, and
the RISC-V targets have width 32/64).  The sum is packaged by `leSumB`; the
remaining step (the `panSetByteHOL` reassembly identity `panSetByteHOL_ofNat_eq`
and the Pan-side induction) is tracked by `flapjack-pxn.18.4.3.111.1.1.2`.
-/

/-- Little-endian integer sum of the bytes with absolute index starting at `k`. -/
def leSumB (k : Nat) (bs : List (BitVec 8)) : Nat :=
  (bs.zipIdx k).foldl (fun (v : Nat) (p : BitVec 8 × Nat) => v + p.1.toNat * 256 ^ p.2) 0

theorem leSumB_foldl_add_eq (l : List (BitVec 8 × Nat)) (acc : Nat) :
    l.foldl (fun (v : Nat) (p : BitVec 8 × Nat) => v + p.1.toNat * 256 ^ p.2) acc
      = acc + l.foldl (fun (v : Nat) (p : BitVec 8 × Nat) => v + p.1.toNat * 256 ^ p.2) 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons p t ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + p.1.toNat * 256 ^ p.2), ih (0 + p.1.toNat * 256 ^ p.2)]
      omega

theorem leSumB_cons (k : Nat) (b : BitVec 8) (rest : List (BitVec 8)) :
    leSumB k (b :: rest) = b.toNat * 256 ^ k + leSumB (k + 1) rest := by
  simp only [leSumB, List.zipIdx_cons, List.foldl_cons]
  rw [leSumB_foldl_add_eq]
  omega

/-- The Crep decoder of the mapped byte list is the little-endian integer sum. -/
theorem crepClockWordOfBytes_eq_leSumB {width : Nat} (bs : List (BitVec 8)) :
    crepClockWordOfBytes (bs.map UInt8.ofBitVec)
      = BitVec.ofNat width (leSumB 0 bs) := by
  simp only [crepClockWordOfBytes, leSumB, List.zipIdx_map, List.foldl_map, Prod.map,
    UInt8.toNat_ofBitVec]
  rfl

theorem leSumB_dvd (bs : List (BitVec 8)) (k : Nat) : 256 ^ k ∣ leSumB k bs := by
  induction bs generalizing k with
  | nil => simp [leSumB]
  | cons b rest ih =>
      rw [leSumB_cons]
      refine Nat.dvd_add ⟨b.toNat, by rw [Nat.mul_comm]⟩ ?_
      refine Nat.dvd_trans ⟨256, by rw [Nat.pow_add_one]⟩ (ih (k + 1))

theorem leSumB_add (bs : List (BitVec 8)) (k : Nat) :
    leSumB k bs + 256 ^ k ≤ 256 ^ (k + bs.length) := by
  induction bs generalizing k with
  | nil => simp [leSumB]
  | cons b rest ih =>
      have hb : b.toNat + 1 ≤ 256 := by have := b.isLt; omega
      have h1 : b.toNat * 256 ^ k + 256 ^ k ≤ 256 ^ (k + 1) := by
        calc b.toNat * 256 ^ k + 256 ^ k
            = (b.toNat + 1) * 256 ^ k := by rw [Nat.add_mul]; simp
          _ ≤ 256 * 256 ^ k := Nat.mul_le_mul_right (256 ^ k) hb
          _ = 256 ^ (k + 1) := by rw [Nat.pow_add_one, Nat.mul_comm]
      have ih' := ih (k + 1)
      rw [leSumB_cons, List.length_cons,
        show k + (rest.length + 1) = (k + 1) + rest.length by omega]
      omega

theorem leSumB_lt (bs : List (BitVec 8)) (k : Nat) :
    leSumB k bs < 256 ^ (k + bs.length) := by
  have h := leSumB_add bs k
  have hpos : 0 < 256 ^ k := Nat.pow_pos (by decide)
  omega

/-- Writing the byte `b` at the address `k` (below the byte count `width/8`,
    little-endian) into a little-endian-reassembled cell `V` whose higher byte
    is already clear (`256^(k+1) ∣ V`) yields the byte sum `b * 256^k + V`. -/
theorem panSetByteHOL_ofNat_eq {width : Nat} [NeZero width]
    (k : Nat) (hk : k < width / 8) (b : BitVec 8) (V : Nat)
    (hdvd : 256 ^ (k + 1) ∣ V) (hVlt : V < 2 ^ width) :
    panSetByteHOL (BitVec.ofNat width k) (BitVec.ofNat width b.toNat)
      (BitVec.ofNat width V) false =
      BitVec.ofNat width (b.toNat * 256 ^ k + V) := by
  have hwpos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have hkw : k < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_lt hk) (Nat.div_le_self width 8))
      Nat.lt_two_pow_self
  have hb : b.toNat < 256 := b.isLt
  have hbw : b.toNat < 2 ^ width := Nat.lt_of_lt_of_le hb (by
    calc (256 : Nat) = 2 ^ 8 := by decide
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega))
  have hlow : V % 256 ^ k = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans ⟨256, by rw [Nat.pow_add_one]⟩ hdvd)
  have hhigh : V / (256 ^ k * 256) * (256 ^ k * 256) = V := by
    rw [← Nat.pow_add_one, Nat.div_mul_cancel hdvd]
  simp only [panSetByteHOL, Bool.false_eq_true, if_false, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt hVlt, Nat.mod_eq_of_lt hbw, Nat.mod_eq_of_lt hb,
    hlow, hhigh, Nat.zero_add]

/-- While the written addresses stay below the byte count `width/8`, the exact
    Pan byte decoder reassembles the little-endian byte sum of the list. -/
theorem panWordOfBytesHOL_eq_ofNat_le {width : Nat} [NeZero width]
    (hdiv : width % 8 = 0) (k : Nat) (bs : List (BitVec 8))
    (hk : k + bs.length ≤ width / 8) :
    panWordOfBytesHOL (width := width) false (BitVec.ofNat width k) bs =
      BitVec.ofNat width (leSumB k bs) := by
  have hwpos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  induction bs generalizing k with
  | nil => simp [panWordOfBytesHOL, leSumB]
  | cons b rest ih =>
      have hk1 : k + 1 + rest.length ≤ width / 8 := by
        simp only [List.length_cons] at hk; omega
      have hsucc : (BitVec.ofNat width k : RiscV.Word width) + 1 =
          BitVec.ofNat width (k + 1) := by
        simp [BitVec.ofNat_add]
      rw [panWordOfBytesHOL, leSumB_cons, hsucc, ih (k + 1) hk1]
      refine panSetByteHOL_ofNat_eq k (by omega) b (leSumB (k + 1) rest)
        (leSumB_dvd rest (k + 1)) ?_
      have h := leSumB_lt rest (k + 1)
      have hw8 : 8 * (width / 8) = width := by
        rw [Nat.mul_comm]; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
      have hle8 : 8 * (k + 1 + rest.length) ≤ width := by
        have hm := Nat.mul_le_mul_left 8 hk1
        rwa [hw8] at hm
      have hpow : (256 : Nat) ^ (k + 1 + rest.length) ≤ 2 ^ width := by
        calc (256 : Nat) ^ (k + 1 + rest.length)
            = (2 ^ 8) ^ (k + 1 + rest.length) := by rw [show (256 : Nat) = 2 ^ 8 by decide]
          _ = 2 ^ (8 * (k + 1 + rest.length)) := by rw [Nat.pow_mul]
          _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) hle8
      omega

/-- Kernel-checked regression instances of the decode equality
    `panWordOfBytesHOL false 0 bs = crepClockWordOfBytes (bs.map UInt8.ofBitVec)`
    at widths 8, 16 and the RISC-V width 64, with byte lists longer than one
    word (the FFI-returned `new_bytes` is not length-bounded by the source, so
    the overlong case is the relevant one).  The matching direct HOL oracle for
    the source decoder `word_of_bytes F 0w new_bytes` is captured in
    `scripts/hol-probes/pan_word_of_bytes_overlong_probe.out`. -/
example : panWordOfBytesHOL (width := 8) false (0 : RiscV.Word 8) [1, 2, 3]
    = crepClockWordOfBytes ([1, 2, 3].map UInt8.ofBitVec) := by decide

example : panWordOfBytesHOL (width := 16) false (0 : RiscV.Word 16) [1, 2, 3, 4, 5]
    = crepClockWordOfBytes ([1, 2, 3, 4, 5].map UInt8.ofBitVec) := by decide

example : panWordOfBytesHOL (width := 64) false (0 : RiscV.Word 64)
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    = crepClockWordOfBytes ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map UInt8.ofBitVec) := by decide

example : panWordOfBytesHOL (width := 64) false (0 : RiscV.Word 64) [255, 1]
    = crepClockWordOfBytes ([255, 1].map UInt8.ofBitVec) := by decide

end Flapjack
