import Flapjack.Compiler.Backend.Semantics.WordSem
import Flapjack.Pancake.Semantics.ByteAlignBridge
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact

/-!
# crep_to_loop `write_bytearray_mem_rel` over the exact carriers

Exact port of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`write_bytearray_mem_rel` (251) over the exact `mem_rel`
(`crepToLoopMemRelHOLExact`), the tagged `panSem$write_bytearray`
(`panWriteBytearrayWord8HOL`) and `wordSem$write_bytearray`
(`writeBytearrayExact`) (bead `flapjack-pxn.18.5.6.17.1.3`).

HOL passes one address set `dm : 'a word set` to both `write_bytearray`s and to
`mem_rel`.  The Lean wordSem port reads its domain as a `Bool` predicate and the
panSem port and `mem_rel` as a `Prop` predicate, so HOL's single set is `dm :
BitVec width → Bool` and the `Prop` views are `fun a => dm a = true`, the
set-as-Bool rendering used by the tagged exact `state_rel`.  No width premise is
needed: the byte-write bridge below holds at every positive width.
-/

namespace Flapjack

private theorem setWidth_eq_ofNat8 {width : Nat} (b : BitVec 8) :
    b.setWidth width = BitVec.ofNat width b.toNat := by
  apply BitVec.eq_of_toNat_eq; simp

private theorem panSetByteHOL_eq_setByteHOL8_ge {width : Nat} [NeZero width] (h8 : 8 ≤ width)
    (a v : BitVec width) (b : BitVec 8) (be : Bool) :
    panSetByteHOL a (BitVec.ofNat width b.toNat) v be = setByteHOL8 a b v be := by
  have hu : (UInt8.ofNat b.toNat).toNat = b.toNat := by
    simp
  have := panSetByteHOL_eq_riscvSetByteHOL h8 a v (UInt8.ofNat b.toNat) be
  rw [hu] at this
  rw [this]
  simp only [riscvSetByteHOL, setByteHOL8, byteIndexHOL, setWidth_eq_ofNat8, hu]

private theorem two_pow_dvd_of_le {w n : Nat} (h : w ≤ n) : 2 ^ w ∣ 2 ^ n :=
  Nat.pow_dvd_pow 2 h

private theorem mod255_small {w : Nat} (h8 : w < 8) : 255 % 2 ^ w = 2 ^ w - 1 := by
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  obtain ⟨m, hm⟩ := two_pow_dvd_of_le (show w ≤ 8 by omega)
  have h256 : (256 : Nat) = 2 ^ w * m := by simpa using hm
  have hm1 : 1 ≤ m := by
    rcases m with _ | m
    · simp at h256
    · omega
  have hle : 2 ^ w ≤ 2 ^ w * m := Nat.le_mul_of_pos_right _ hm1
  have : 255 = 2 ^ w * (m - 1) + (2 ^ w - 1) := by
    have : 2 ^ w * (m - 1) = 2 ^ w * m - 2 ^ w := by
      rw [Nat.mul_sub, Nat.mul_one]
    omega
  rw [this, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (Nat.sub_lt hpos Nat.one_pos)

private theorem shiftLeft_zero_of_ge {w : Nat} (x : BitVec w) {n : Nat} (h : w ≤ n) :
    x <<< n = 0#w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_zero, Nat.shiftLeft_eq]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (two_pow_dvd_of_le h) (Nat.dvd_mul_left _ _))

private theorem panSetByteHOL_eq_setByteHOL8_lt {width : Nat} [NeZero width] (h8 : width < 8)
    (a v : BitVec width) (b : BitVec 8) (be : Bool) :
    panSetByteHOL a (BitVec.ofNat width b.toNat) v be = setByteHOL8 a b v be := by
  have hd : width / 8 = 0 := Nat.div_eq_of_lt h8
  have hw256 : 2 ^ width ≤ 256 := by
    have : 2 ^ width ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hv : v.toNat < 256 := Nat.lt_of_lt_of_le v.isLt hw256
  have hb : b.toNat % 2 ^ width < 256 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos width)) hw256
  have zero_case : (v.toNat % 1 + b.toNat % 2 ^ width % 256 + v.toNat / 256 * 256) % 2 ^ width =
      (v.toNat &&& 2 ^ width - 1 - 255 % 2 ^ width ||| b.toNat % 2 ^ width) := by
    rw [mod255_small h8, Nat.sub_self, Nat.and_zero, Nat.zero_or, Nat.mod_one,
      Nat.div_eq_of_lt hv, Nat.mod_eq_of_lt hb]
    simp
  apply BitVec.eq_of_toNat_eq
  unfold panSetByteHOL setByteHOL8 byteIndexHOL
  simp only [hd, Nat.mod_zero]
  cases be
  · simp only [Bool.false_eq_true, if_false]
    by_cases ha : a.toNat = 0
    · simp [ha]
      exact zero_case
    · have hge : width ≤ 8 * a.toNat := by omega
      rw [shiftLeft_zero_of_ge _ hge, shiftLeft_zero_of_ge _ hge]
      have hpow : 2 ^ width ∣ 256 ^ a.toNat := by
        rw [pow256_eq_two_pow_mul]; exact two_pow_dvd_of_le hge
      have h256a : 256 ≤ 256 ^ a.toNat :=
        Nat.le_self_pow ha 256
      simp only [BitVec.toNat_ofNat, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_not,
        ]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv h256a),
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hv (Nat.le_trans h256a (Nat.le_mul_of_pos_right _ (by decide)))),
        Nat.zero_mul, Nat.add_zero]
      obtain ⟨k, hk⟩ := hpow
      rw [hk, ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ width), Nat.mul_assoc, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt v.isLt]
      simp
  · simp
    exact zero_case

/-- Flapjack bridge (no HOL declaration): the panSem and wordSem renderings of
    HOL `byte$set_byte` agree at every positive width. This public helper is
    also used by the exact `ncompile_correct` Store32 case to compare the two
    evaluator memory-update chains. -/
theorem panSetByteHOL_eq_setByteHOL8 {width : Nat} [NeZero width]
    (a v : BitVec width) (b : BitVec 8) (be : Bool) :
    panSetByteHOL a (BitVec.ofNat width b.toNat) v be = setByteHOL8 a b v be := by
  by_cases h8 : 8 ≤ width
  · exact panSetByteHOL_eq_setByteHOL8_ge h8 a v b be
  · exact panSetByteHOL_eq_setByteHOL8_lt (by omega) a v b be

/-- Exact HOL `write_bytearray_mem_rel` (`crep_to_loopProofScript.sml:251-256`):
    `!nb sm tm w dm be. mem_rel sm tm dm ==>
      mem_rel (write_bytearray w nb sm dm be) (write_bytearray w nb tm dm be) dm`. -/
-- Source review: HOL251-256 and its proof use the common byte_align
-- symbolically. The induction preserves tail-first writes and returns the
-- original outer memory on failure. The proof requires the two Lean writers
-- to use the same alignment, but no numeric LOG2 theorem: it works with any
-- common alignment at every positive width. The numeric executable definitions
-- remain unchanged; this port assumes no equality with HOL's unspecified LOG2 0.
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "write_bytearray_mem_rel"
  (words_as_type_indexed_bitvec)]
theorem write_bytearray_mem_rel {width : Nat} [NeZero width] :
    ∀ (nb : List (BitVec 8)) (sm : BitVec width → HolWordLab width)
      (tm : BitVec width → WordLocW width) (w : BitVec width) (dm : BitVec width → Bool)
      (be : Bool),
      crepToLoopMemRelHOLExact sm tm (fun a => dm a = true) →
      crepToLoopMemRelHOLExact (panWriteBytearrayWord8HOL w nb sm (fun a => dm a = true) be)
        (writeBytearrayExact w nb tm dm be) (fun a => dm a = true) := by
  intro nb
  induction nb with
  | nil => intro sm tm w dm be h; exact h
  | cons b bs ih =>
    intro sm tm w dm be h
    have hr := ih sm tm (w + 1) dm be h
    simp only [panWriteBytearrayWord8HOL, writeBytearrayExact]
    generalize panWriteBytearrayWord8HOL (w + 1) bs sm (fun a => dm a = true) be = pr at hr ⊢
    generalize writeBytearrayExact (w + 1) bs tm dm be = tr at hr ⊢
    have hal : riscvByteAlignHOL w = panByteAlignHOL w := riscvByteAlignHOL_eq_panByteAlignHOL w
    cases hc : pr (panByteAlignHOL w) with
    | word cell =>
      by_cases hd : dm (panByteAlignHOL w) = true
      · have htr : tr (panByteAlignHOL w) = .word cell := by
          rw [← hr _ hd, hc]; rfl
        simp only [panMemStoreByteWord8HOL, hc, hd, if_true, memStoreByteAuxExact, hal, htr]
        intro ad had
        by_cases hadal : ad = panByteAlignHOL w
        · subst hadal
          simp only [wlabWlocExact, if_true]
          rw [panSetByteHOL_eq_setByteHOL8]
        · simp only [hadal, if_false]
          exact hr ad had
      · have hdf : dm (panByteAlignHOL w) = false := by simpa using hd
        simp only [panMemStoreByteWord8HOL, hc, hdf, memStoreByteAuxExact, hal]
        cases tr (panByteAlignHOL w) <;> simp <;> exact h

/-- Flapjack-specific dependency analysis, not a second executable port:
these helpers abstract only the common alignment used by the two native writers.
No HOL tag is claimed for this additional parameterization. -/
def panMemStoreByteWord8HOLAligned {width : Nat} [NeZero width] (alignment : BitVec width → BitVec width)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) (byte : BitVec 8) :
    Option (RiscV.Word width → HolWordLab width) :=
  let aligned := alignment address
  match memory aligned with
  | .word cell =>
      if domain aligned then
        some (fun current =>
          if current = aligned then
            .word (panSetByteHOL address (BitVec.ofNat width byte.toNat) cell
              bigEndian)
          else memory current)
      else none

def panWriteBytearrayWord8HOLAligned {width : Nat} [NeZero width] (alignment : BitVec width → BitVec width)
    (address : RiscV.Word width) (bytes : List (BitVec 8))
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) : RiscV.Word width → HolWordLab width :=
  match bytes with
  | [] => memory
  | byte :: rest =>
      match panMemStoreByteWord8HOLAligned alignment
          (panWriteBytearrayWord8HOLAligned alignment (address + 1) rest memory domain bigEndian)
          domain bigEndian address byte with
      | some updated => updated
      | none => memory


def memStoreByteAuxExactAligned {width : Nat} [NeZero width] (alignment : BitVec width → BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bigEndian : Bool) (address : BitVec width) (byte : BitVec 8) :
    Option (BitVec width → WordLocW width) :=
  match memory (alignment address) with
  | .word v =>
      if domain (alignment address) then
        some (fun a => if a = alignment address then
          .word (setByteHOL8 address byte v bigEndian) else memory a)
      else none
  | _ => none

def writeBytearrayExactAligned {width : Nat} [NeZero width] (alignment : BitVec width → BitVec width) (address : BitVec width) :
    List (BitVec 8) → (BitVec width → WordLocW width) → (BitVec width → Bool) → Bool →
      BitVec width → WordLocW width
  | [], memory, _, _ => memory
  | b :: bs, memory, domain, bigEndian =>
      match memStoreByteAuxExactAligned alignment (writeBytearrayExactAligned alignment (address + 1) bs memory domain bigEndian)
          domain bigEndian address b with
      | some m => m
      | none => memory

/-- The original writer relation is independent of the chosen common alignment.
This is Flapjack-specific infrastructure; the original numeric instance above
retains its HOL tag and unchanged hypotheses. -/
theorem writeBytearrayMemRelAnyAlignment {width : Nat} [NeZero width] (alignment : BitVec width → BitVec width) :
    ∀ (nb : List (BitVec 8)) (sm : BitVec width → HolWordLab width)
      (tm : BitVec width → WordLocW width) (w : BitVec width) (dm : BitVec width → Bool)
      (be : Bool),
      crepToLoopMemRelHOLExact sm tm (fun a => dm a = true) →
      crepToLoopMemRelHOLExact (panWriteBytearrayWord8HOLAligned alignment w nb sm (fun a => dm a = true) be)
        (writeBytearrayExactAligned alignment w nb tm dm be) (fun a => dm a = true) := by
  intro nb
  induction nb with
  | nil => intro sm tm w dm be h; exact h
  | cons b bs ih =>
    intro sm tm w dm be h
    have hr := ih sm tm (w + 1) dm be h
    simp only [panWriteBytearrayWord8HOLAligned, writeBytearrayExactAligned]
    generalize panWriteBytearrayWord8HOLAligned alignment (w + 1) bs sm (fun a => dm a = true) be = pr at hr ⊢
    generalize writeBytearrayExactAligned alignment (w + 1) bs tm dm be = tr at hr ⊢
    cases hc : pr (alignment w) with
    | word cell =>
      by_cases hd : dm (alignment w) = true
      · have htr : tr (alignment w) = .word cell := by
          rw [← hr _ hd, hc]; rfl
        simp only [panMemStoreByteWord8HOLAligned, hc, hd, if_true, memStoreByteAuxExactAligned, htr]
        intro ad had
        by_cases hadal : ad = alignment w
        · subst hadal
          simp only [wlabWlocExact, if_true]
          rw [panSetByteHOL_eq_setByteHOL8]
        · simp only [hadal, if_false]
          exact hr ad had
      · have hdf : dm (alignment w) = false := by simpa using hd
        simp only [panMemStoreByteWord8HOLAligned, hc, hdf, memStoreByteAuxExactAligned]
        cases tr (alignment w) <;> simp <;> exact h


end Flapjack
