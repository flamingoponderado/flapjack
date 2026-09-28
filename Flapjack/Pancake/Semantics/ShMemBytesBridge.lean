import Flapjack.Pancake.Semantics.PanSem.ShMemExact
import Flapjack.Pancake.Semantics.CrepSem.TotalEval
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.ByteAlignBridge
import Flapjack.Pancake.Semantics.PanSem.ByteRoundtrip

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
    (k : Nat) (bs : List (BitVec 8)) (hk : k + bs.length ≤ width / 8) :
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
      have hle8 : 8 * (k + 1 + rest.length) ≤ width := by
        have hm := Nat.mul_le_mul_left 8 hk1
        have hmm : 8 * (width / 8) ≤ width := by
          rw [Nat.mul_comm]; exact Nat.div_mul_le_self width 8
        omega
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

/-! ## Address-parameterised decoder and its concatenation law

`panWacc a bs C` is `panWordOfBytesHOL false (ofNat width a) bs` with the
decoded cell kept explicit (head byte outermost at the lowest address).  The
concatenation law exposes how a byte list splits into its first `bs.length`
bytes (applied to the accumulator) and its continuation (applied deeper).
This is the stepping stone for the unconditional overlong equality: once
`panWacc a l` is shown independent of its cell argument for `l.length = width/8`
(every residue is written exactly once), the continuation `e` is erased. -/

/-- Address-parameterised exact Pan byte decoder with explicit accumulator. -/
def panWacc {width : Nat} [NeZero width] (a : Nat) :
    List (BitVec 8) → RiscV.Word width → RiscV.Word width
  | [], C => C
  | b :: bs, C =>
      panSetByteHOL (BitVec.ofNat width a) (BitVec.ofNat width b.toNat) (panWacc (a + 1) bs C) false

/-- `panWordOfBytesHOL` is `panWacc` started from the zero cell, for any address
    whose `Nat` value plus the list length does not overflow the word. -/
theorem panWordOfBytesHOL_eq_panWacc {width : Nat} [NeZero width] (bs : List (BitVec 8))
    (a : Nat) (ha : a + bs.length ≤ 2 ^ width) :
    panWordOfBytesHOL (width := width) false (BitVec.ofNat width a) bs = panWacc a bs 0 := by
  induction bs generalizing a with
  | nil => simp [panWordOfBytesHOL, panWacc]
  | cons b rest ih =>
      have ha' : a + 1 + rest.length ≤ 2 ^ width := by simp only [List.length_cons] at ha; omega
      have hsucc : (BitVec.ofNat width a : RiscV.Word width) + 1 = BitVec.ofNat width (a + 1) := by
        simp [BitVec.ofNat_add]
      rw [panWordOfBytesHOL, hsucc, ih (a + 1) ha', panWacc]

/-- Concatenation law for `panWacc`: a byte list splits into its first
    `bs.length` bytes, applied to the accumulator at address `a`, and the
    continuation `es`, applied deeper at address `a + bs.length`. -/
theorem panWacc_append {width : Nat} [NeZero width] (bs es : List (BitVec 8)) (a : Nat)
    (C : RiscV.Word width) :
    panWacc a (bs ++ es) C = panWacc a bs (panWacc (a + bs.length) es C) := by
  induction bs generalizing a C with
  | nil => simp [panWacc]
  | cons b rest ih =>
      simp only [List.cons_append, List.length_cons, panWacc]
      rw [ih (a + 1) C]
      have h : a + 1 + rest.length = a + (rest.length + 1) := by omega
      rw [h]


/-! ## Byte write/read projection at the written residue

`panGetByteHOL_panSetByteHOL_self` reads back the byte just written at the same
address, i.e. `panSetByteHOL` replaces the byte at the written residue.  This is
the core projection fact for the overlong truncation argument: a later write at
the same residue erases the earlier byte. -/

/-- `2 ^ (8 * e) = 256 ^ e`. -/
theorem two_pow_eight_mul_eq_pow256 (e : Nat) : (2 : Nat) ^ (8 * e) = 256 ^ e := by
  rw [show (256 : Nat) = 2 ^ 8 by decide, Nat.pow_mul]

/-- `2 ^ (8 * e + 8) = 256 ^ (e + 1)`. -/
theorem two_pow_eight_mul_succ_eq_pow256 (e : Nat) :
    (2 : Nat) ^ (8 * e + 8) = 256 ^ (e + 1) := by
  have h : 8 * e + 8 = 8 * (e + 1) := by omega
  rw [h, show (256 : Nat) = 2 ^ 8 by decide, Nat.pow_mul]

/-- Reading back the byte just written at the same address (little-endian) returns
    that byte: `panSetByteHOL` overwrites the byte at the written residue. -/
theorem panGetByteHOL_panSetByteHOL_self {width : Nat} [NeZero width]
    (hdiv : width % 8 = 0) (k : Nat) (hk : k < width / 8) (b : BitVec 8)
    (X : RiscV.Word width) :
    (panGetByteHOL (BitVec.ofNat width k)
        (panSetByteHOL (BitVec.ofNat width k) (BitVec.ofNat width b.toNat) X false)
        false).toNat = b.toNat := by
  have hkw : k < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_lt hk) (Nat.div_le_self width 8))
      Nat.lt_two_pow_self
  have haddr : (BitVec.ofNat width k : RiscV.Word width).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkw]
  have hbi : byteBitIndex (BitVec.ofNat width k) false = 8 * k := by
    simp only [byteBitIndex, Bool.false_eq_true, if_false, haddr, Nat.mod_eq_of_lt hk]
  have h256 : 0 < 256 ^ k := Nat.pow_pos (by decide)
  have hlow : X.toNat % 256 ^ k < 256 ^ k := Nat.mod_lt _ h256
  have hb : b.toNat < 256 := b.isLt
  have hbb : (UInt8.ofNat b.toNat).toNat = b.toNat := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt b.isLt]
  have h8 : 8 ≤ width :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne width)) (Nat.dvd_of_mod_eq_zero hdiv)
  have hset := panSetByteHOL_toNat (width := width) h8 (BitVec.ofNat width k)
    X (UInt8.ofNat b.toNat) false
  rw [hbi, two_pow_eight_mul_eq_pow256, two_pow_eight_mul_succ_eq_pow256, hbb] at hset
  simp only [panGetByteHOL, Bool.false_eq_true, if_false, haddr, Nat.mod_eq_of_lt hk]
  rw [UInt8.toNat_ofNat', Nat.mod_mod, hset]
  have harr : BitVec.toNat X / 256 ^ (k + 1) * 256 ^ (k + 1) +
        b.toNat * 256 ^ k + BitVec.toNat X % 256 ^ k
      = 256 ^ k * (256 * (BitVec.toNat X / 256 ^ (k + 1))) +
        (b.toNat * 256 ^ k + BitVec.toNat X % 256 ^ k) := by
    rw [Nat.pow_add_one]
    ac_rfl
  rw [harr, Nat.mul_add_div h256]
  have hbc : (b.toNat * 256 ^ k + BitVec.toNat X % 256 ^ k) / 256 ^ k = b.toNat := by
    rw [Nat.add_comm, Nat.mul_comm b.toNat (256 ^ k), Nat.add_mul_div_left _ _ h256,
      Nat.div_eq_of_lt hlow, Nat.zero_add]
  rw [hbc]
  rw [show 256 * (BitVec.toNat X / 256 ^ (k + 1)) + b.toNat
      = b.toNat + (BitVec.toNat X / 256 ^ (k + 1)) * 256 by
        rw [Nat.mul_comm 256 (BitVec.toNat X / 256 ^ (k + 1)), Nat.add_comm]]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-! ## Windowed byte reconstruction

`panBytesFrom a n X` is the list of the `BitVec 8` bytes `panGetByteHOL` reads at
addresses `a, a+1, ..., a+n-1` of `X`.  `panWacc_panBytesFrom_eq_self` is the
matching roundtrip: writing back over a cell the bytes read from a word that
agrees with the cell on the whole window leaves the cell unchanged.  These are
the windowed building blocks for the overlong truncation argument.
-/

theorem div_pow_mod_eq (v r : Nat) : (v / 256 ^ r) % 256 = v % 256 ^ (r + 1) / 256 ^ r := by
  rw [Nat.pow_succ]
  rw [Nat.mod_mul_right_div_self]

/-- The bytes `get_byte` at addresses `a, a+1, ..., a+n-1` of a word, as the
    `BitVec 8` list that `panWacc`/`panWordOfBytesHOL` consume. -/
def panBytesFrom {width : Nat} [NeZero width] (a : Nat) :
    Nat → RiscV.Word width → List (BitVec 8)
  | 0, _ => []
  | n + 1, X => (panGetByteHOL (BitVec.ofNat width a) X false).toBitVec ::
      panBytesFrom (a + 1) n X

theorem panBytesFrom_eq_of_getByte_eq {width : Nat} [NeZero width] {a n : Nat}
    {X Y : RiscV.Word width}
    (h : ∀ j, j < n → panGetByteHOL (BitVec.ofNat width (a + j)) X false
      = panGetByteHOL (BitVec.ofNat width (a + j)) Y false) :
    panBytesFrom a n X = panBytesFrom a n Y := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      simp only [panBytesFrom]
      have h0 := h 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0, ih (a := a + 1) (fun j hj => by
        have := h (j + 1) (by omega)
        simpa only [show a + (j + 1) = a + 1 + j by omega] using this)]

theorem panWacc_panBytesFrom_eq_self {width : Nat} [NeZero width] (hwidth : 8 ≤ width)
    (n : Nat) : ∀ (a : Nat) (X C : RiscV.Word width),
      (∀ j, j < n → panGetByteHOL (BitVec.ofNat width (a + j)) C false
        = panGetByteHOL (BitVec.ofNat width (a + j)) X false) →
      panWacc a (panBytesFrom a n X) C = C := by
  induction n with
  | zero => intro a X C _; rfl
  | succ n ih =>
      intro a X C h
      simp only [panBytesFrom, panWacc]
      rw [ih (a + 1) X C (fun j hj => by
        have := h (j + 1) (by omega)
        simpa only [show a + (j + 1) = a + 1 + j by omega] using this)]
      have h0 := h 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [← h0, UInt8.toNat_toBitVec]
      exact panSetByteHOL_panGetByteHOL (BitVec.ofNat width a) C false hwidth


/-! ## Byte-level word extensionality

Two `RiscV.Word width` values with the same little-endian byte at every residue
`r < width / 8` are equal, via base-256 digit injectivity.  This turns agreement
of the `panGetByteHOL` projections into equality of the words. -/

/-- Base-256 digit injectivity: two natural numbers below `256 ^ p` whose
    base-256 digits agree at every position `< p` are equal. -/
theorem nat_digits_inj (a b p : Nat)
    (h : ∀ r, r < p → (a / 256^r) % 256 = (b / 256^r) % 256)
    (ha : a < 256^p) (hb : b < 256^p) : a = b := by
  induction p generalizing a b with
  | zero => omega
  | succ p ih =>
      have h0 : a % 256 = b % 256 := by
        have hh := h 0 (by omega)
        simpa using hh
      have hshift : ∀ r, r < p → ((a / 256) / 256^r) % 256 = ((b / 256) / 256^r) % 256 := by
        intro r hr
        have hh := h (r + 1) (by omega)
        have hpow : 256 ^ (r + 1) = 256 * 256 ^ r := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow] at hh
        simpa only [Nat.div_div_eq_div_mul] using hh
      have hpowp : 256 ^ (p + 1) = 256 ^ p * 256 := Nat.pow_succ 256 p
      rw [hpowp] at ha hb
      have ha' : a / 256 < 256 ^ p := (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr ha
      have hb' : b / 256 < 256 ^ p := (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr hb
      have heq : a / 256 = b / 256 := ih (a / 256) (b / 256) hshift ha' hb'
      have ea : a % 256 + 256 * (a / 256) = a := Nat.mod_add_div a 256
      have eb : b % 256 + 256 * (b / 256) = b := Nat.mod_add_div b 256
      omega

/-- `panGetByteHOL` at address `r` is the `r`-th little-endian base-256 digit. -/
theorem panGetByteHOL_toNat_ofNat {width : Nat} [NeZero width] (r : Nat)
    (hr : r < width / 8) (X : RiscV.Word width) :
    (panGetByteHOL (BitVec.ofNat width r) X false).toNat = (X.toNat / 256^r) % 256 := by
  have hkw : r < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_lt hr) (Nat.div_le_self width 8))
      Nat.lt_two_pow_self
  have h256 : 0 < 256 ^ r := Nat.pow_pos (by decide)
  simp only [panGetByteHOL, Bool.false_eq_true, if_false, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hr]
  rw [UInt8.toNat_ofNat', show (2 : Nat) ^ 8 = 256 by decide]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 256))

/-- Word extensionality from bytes: two words whose little-endian bytes agree at
    every residue `r < width / 8` are equal. -/
theorem panWord_eq_of_getByte_eq {width : Nat} [NeZero width] (hdiv : width % 8 = 0)
    {X Y : RiscV.Word width}
    (h : ∀ r, r < width / 8 →
      (panGetByteHOL (BitVec.ofNat width r) X false).toNat
        = (panGetByteHOL (BitVec.ofNat width r) Y false).toNat) : X = Y := by
  apply BitVec.eq_of_toNat_eq
  have hw8 : 8 * (width / 8) = width := by
    rw [Nat.mul_comm]; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  have hpow : (2 : Nat) ^ width = 256 ^ (width / 8) :=
    calc (2 : Nat) ^ width = 2 ^ (8 * (width / 8)) := congrArg (fun e => (2 : Nat) ^ e) hw8.symm
      _ = 256 ^ (width / 8) := two_pow_eight_mul_eq_pow256 (width / 8)
  refine nat_digits_inj X.toNat Y.toNat (width / 8) ?_ ?_ ?_
  · intro r hr
    rw [← panGetByteHOL_toNat_ofNat r hr X, ← panGetByteHOL_toNat_ofNat r hr Y]
    exact h r hr
  · exact Nat.lt_of_lt_of_eq X.isLt hpow
  · exact Nat.lt_of_lt_of_eq Y.isLt hpow


/-! ## Address-parameterised decoder `toNat` characterization

The bridge from the byte-level decoder to the little-endian sum: for an address
`a` and a word cell `C`, `panWacc a l C` keeps the low `a` residues of `C`, the
high part of `C` above the written window, and contributes `leSumB a l` on the
window. -/


theorem mul_div_self_of_add_of_dvd {m D X L : Nat} (hm : 0 < m) (hd : m ∣ D)
    (hX : X = L + D) (hL : L < m) : X / m * m = D := by
  subst hX
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hL, Nat.zero_add, Nat.mul_comm]

theorem mod_eq_of_add_of_dvd {m D X L : Nat} (hd : m ∣ D) (hX : X = L + D) :
    X % m = L % m := by
  subst hX
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.add_mul_mod_self_left]

theorem panWacc_toNat_formula {width : Nat} [NeZero width] (h8w : 8 ≤ width)
    (l : List (BitVec 8)) (a : Nat) (C : RiscV.Word width)
    (ha : a + l.length ≤ width / 8) :
    (panWacc a l C).toNat =
      leSumB a l + (C.toNat / 256 ^ (a + l.length)) * 256 ^ (a + l.length)
        + C.toNat % 256 ^ a := by
  induction l generalizing a with
  | nil =>
      simp only [panWacc, leSumB, List.zipIdx_nil, List.foldl_nil, List.length_nil,
        Nat.add_zero, Nat.zero_add]
      rw [Nat.mul_comm (C.toNat / 256 ^ a) (256 ^ a)]
      exact (Nat.div_add_mod C.toNat (256 ^ a)).symm
  | cons b rest ih =>
      have ha1 : a + 1 + rest.length ≤ width / 8 := by
        simp only [List.length_cons] at ha; omega
      have halt : a < width / 8 := by omega
      have hbi : byteBitIndex (BitVec.ofNat width a) false = 8 * a := by
        have hkw : a < 2 ^ width :=
          Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_lt halt) (Nat.div_le_self width 8))
            Nat.lt_two_pow_self
        have haddr : (BitVec.ofNat width a : RiscV.Word width).toNat = a := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkw]
        simp only [byteBitIndex, Bool.false_eq_true, if_false, haddr, Nat.mod_eq_of_lt halt]
      have hset := panSetByteHOL_toNat (width := width) h8w (BitVec.ofNat width a)
        (panWacc (a + 1) rest C) (UInt8.ofNat b.toNat) false
      have hbb : BitVec.ofNat width (UInt8.ofNat b.toNat).toNat = BitVec.ofNat width b.toNat := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt b.isLt]
      have hbb2 : (UInt8.ofNat b.toNat).toNat = b.toNat := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt b.isLt]
      rw [hbb, hbi, two_pow_eight_mul_eq_pow256 a,
        two_pow_eight_mul_succ_eq_pow256 a] at hset
      rw [ih (a + 1) ha1] at hset
      simp only [panWacc, List.length_cons]
      rw [hset]
      rw [show a + (rest.length + 1) = a + 1 + rest.length by omega]
      generalize hS : leSumB (a + 1) rest = S
      generalize hq : C.toNat / 256 ^ (a + 1 + rest.length) = q
      generalize hLdef : C.toNat % 256 ^ (a + 1) = L
      have hm1 : 0 < 256 ^ (a + 1) := Nat.pow_pos (by decide)
      have hSd1 : 256 ^ (a + 1) ∣ S := by rw [← hS]; exact leSumB_dvd rest (a + 1)
      have hHd1 : 256 ^ (a + 1) ∣ q * 256 ^ (a + 1 + rest.length) :=
        ⟨q * 256 ^ rest.length, by rw [Nat.pow_add]; ac_rfl⟩
      have hSH : 256 ^ (a + 1) ∣ S + q * 256 ^ (a + 1 + rest.length) :=
        Nat.dvd_add hSd1 hHd1
      have hX : S + q * 256 ^ (a + 1 + rest.length) + L
          = L + (S + q * 256 ^ (a + 1 + rest.length)) := by ac_rfl
      have hdiv' := mul_div_self_of_add_of_dvd (m := 256 ^ (a + 1))
        (D := S + q * 256 ^ (a + 1 + rest.length))
        (X := S + q * 256 ^ (a + 1 + rest.length) + L) (L := L)
        hm1 hSH hX (by rw [← hLdef]; exact Nat.mod_lt _ hm1)
      have hSd0 : 256 ^ a ∣ S := Nat.dvd_trans ⟨256, by rw [Nat.pow_add_one]⟩ hSd1
      have hHd0 : 256 ^ a ∣ q * 256 ^ (a + 1 + rest.length) :=
        ⟨q * 256 ^ (1 + rest.length), by
          rw [show a + 1 + rest.length = a + (1 + rest.length) by omega, Nat.pow_add]
          ac_rfl⟩
      have hSH0 : 256 ^ a ∣ S + q * 256 ^ (a + 1 + rest.length) :=
        Nat.dvd_add hSd0 hHd0
      have hmod' := mod_eq_of_add_of_dvd (m := 256 ^ a)
        (D := S + q * 256 ^ (a + 1 + rest.length))
        (X := S + q * 256 ^ (a + 1 + rest.length) + L) (L := L) hSH0 hX
      rw [hdiv', hmod', ← hLdef,
        show 256 ^ (a + 1) = 256 ^ a * 256 by rw [Nat.pow_succ, Nat.mul_comm],
        Nat.mod_mul_right_mod, leSumB_cons, ← hS]
      rw [hbb2]
      ac_rfl



/-! ## Unconditional exact Pan/Crep byte-decoder equality

This is the final step of the shared-memory byte bridge: the exact Pan decoder
`panWordOfBytesHOL false 0` and the Crep `crepClockWordOfBytes` agree on every
byte list for positive widths divisible by 8 (the FFI-returned byte list is not
length-bounded, so the overlong case matters; see the HOL probe
`scripts/hol-probes/pan_word_of_bytes_overlong_probe.out`).  The key facts are the
`toNat` characterization `panWacc_toNat_formula`, cell-independence
`panWacc_indep_len` for lists of length `width / 8`, the address-parameterised
bypass `panWordOfBytesHOL_eq_panWacc_unbounded`, and the truncation
`ofNat_leSumB_take`. -/

theorem panWordOfBytesHOL_eq_panWacc_unbounded {width : Nat} [NeZero width]
    (bs : List (BitVec 8)) (a : Nat) :
    panWordOfBytesHOL (width := width) false (BitVec.ofNat width a) bs = panWacc a bs 0 := by
  induction bs generalizing a with
  | nil => simp [panWordOfBytesHOL, panWacc]
  | cons b rest ih =>
      have hsucc : (BitVec.ofNat width a : RiscV.Word width) + 1 = BitVec.ofNat width (a + 1) := by
        simp [BitVec.ofNat_add]
      rw [panWordOfBytesHOL, hsucc, ih (a + 1), panWacc]

theorem panWacc_indep_len {width : Nat} [NeZero width] (hdiv : width % 8 = 0)
    (l : List (BitVec 8)) (hl : l.length = width / 8) (C : RiscV.Word width) :
    panWacc 0 l C = BitVec.ofNat width (leSumB 0 l) := by
  have hw8 : 8 * (width / 8) = width := by
    rw [Nat.mul_comm]; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  have hp : (2 : Nat) ^ width = 256 ^ (width / 8) :=
    calc (2 : Nat) ^ width = 2 ^ (8 * (width / 8)) := congrArg (fun e => (2 : Nat) ^ e) hw8.symm
      _ = 256 ^ (width / 8) := two_pow_eight_mul_eq_pow256 (width / 8)
  have hC : C.toNat < 256 ^ (width / 8) := by rw [← hp]; exact C.isLt
  have hmid : C.toNat / 256 ^ (0 + l.length) = 0 := by
    rw [Nat.zero_add, hl]; exact Nat.div_eq_of_lt hC
  have hlow : C.toNat % 256 ^ 0 = 0 := Nat.mod_one C.toNat
  have hL : (panWacc 0 l C).toNat = leSumB 0 l := by
    have h8w : 8 ≤ width :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne width)) (Nat.dvd_of_mod_eq_zero hdiv)
    rw [panWacc_toNat_formula h8w l 0 C (by omega), hmid, hlow, Nat.zero_mul, Nat.add_zero]
  have hlt0 : leSumB 0 l < 2 ^ width := by
    have h := leSumB_lt l 0
    rw [Nat.zero_add, hl] at h
    rwa [hp]
  apply BitVec.eq_of_toNat_eq
  rw [hL, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt0]

theorem leSumB_append (l e : List (BitVec 8)) (k : Nat) :
    leSumB k (l ++ e) = leSumB k l + leSumB (k + l.length) e := by
  induction l generalizing k with
  | nil => simp [leSumB]
  | cons b rest ih =>
      simp only [List.cons_append, List.length_cons, leSumB_cons]
      rw [ih (k + 1)]
      rw [show k + 1 + rest.length = k + (rest.length + 1) by omega]
      ac_rfl

theorem ofNat_leSumB_take {width : Nat} [NeZero width] (hdiv : width % 8 = 0)
    (bs : List (BitVec 8)) :
    BitVec.ofNat width (leSumB 0 (bs.take (width / 8))) = BitVec.ofNat width (leSumB 0 bs) := by
  by_cases hle : bs.length ≤ width / 8
  · rw [List.take_of_length_le hle]
  · have hlt : width / 8 < bs.length := Nat.lt_of_not_le hle
    have hlen : (bs.take (width / 8)).length = width / 8 := by
      rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hlt)
    have hw8 : 8 * (width / 8) = width := by
      rw [Nat.mul_comm]; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
    have hp : (2 : Nat) ^ width = 256 ^ (width / 8) :=
      calc (2 : Nat) ^ width = 2 ^ (8 * (width / 8)) := congrArg (fun e => (2 : Nat) ^ e) hw8.symm
        _ = 256 ^ (width / 8) := two_pow_eight_mul_eq_pow256 (width / 8)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hsplit : leSumB 0 bs = leSumB 0 (bs.take (width / 8)) +
        leSumB (0 + (bs.take (width / 8)).length) (bs.drop (width / 8)) := by
      rw [← leSumB_append, List.take_append_drop (width / 8) bs]
    have hdvd : 256 ^ (width / 8) ∣
        leSumB (0 + (bs.take (width / 8)).length) (bs.drop (width / 8)) := by
      rw [hlen, Nat.zero_add]
      exact leSumB_dvd (bs.drop (width / 8)) (width / 8)
    rw [hsplit]
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, hp]
    rw [Nat.add_mul_mod_self_left]

theorem panWordOfBytesHOL_eq_crepClockWordOfBytes {width : Nat} [NeZero width]
    (hdiv : width % 8 = 0) (bs : List (BitVec 8)) :
    panWordOfBytesHOL (width := width) false 0 bs
      = crepClockWordOfBytes (bs.map UInt8.ofBitVec) := by
  by_cases hle : bs.length ≤ width / 8
  · rw [show (0 : RiscV.Word width) = BitVec.ofNat width 0 from rfl]
    rw [panWordOfBytesHOL_eq_ofNat_le 0 bs (by omega)]
    exact (crepClockWordOfBytes_eq_leSumB bs).symm
  · have hlt : width / 8 < bs.length := Nat.lt_of_not_le hle
    have hlen : (bs.take (width / 8)).length = width / 8 := by
      rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hlt)
    calc panWordOfBytesHOL (width := width) false 0 bs
        = panWacc 0 bs 0 := panWordOfBytesHOL_eq_panWacc_unbounded bs 0
      _ = panWacc 0 (bs.take (width / 8)) (panWacc (width / 8) (bs.drop (width / 8)) 0) := by
          have h1 : panWacc 0 bs 0
              = panWacc 0 (bs.take (width / 8) ++ bs.drop (width / 8)) 0 :=
            congrArg (fun l : List (BitVec 8) => panWacc (width := width) 0 l 0)
              (List.take_append_drop (width / 8) bs).symm
          rw [h1, panWacc_append, hlen, Nat.zero_add]
      _ = BitVec.ofNat width (leSumB 0 (bs.take (width / 8))) :=
          panWacc_indep_len (width := width) hdiv (bs.take (width / 8)) hlen
            (panWacc (width / 8) (bs.drop (width / 8)) 0)
      _ = BitVec.ofNat width (leSumB 0 bs) := ofNat_leSumB_take hdiv bs
      _ = crepClockWordOfBytes (bs.map UInt8.ofBitVec) :=
          (crepClockWordOfBytes_eq_leSumB bs).symm

end Flapjack
