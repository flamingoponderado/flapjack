module

public import Flapjack.Basis.Pure.MlString

@[expose] public section

/-! Conversions between HOL byte characters and words. -/
namespace Flapjack.Basis.Pure.MlString

/-- Convert a HOL byte character to its word representation. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "char_to_word8_def"]
def charToWord8 (c : HolChar) : BitVec 8 := BitVec.ofNat 8 c.toNat

/-- Convert a byte word to its HOL character representation. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "word8_to_char_def"]
def word8ToChar (w : BitVec 8) : HolChar := BitVec.ofNat 8 w.toNat

/-- Original `char_lt_total`: the byte order on characters is total. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "char_lt_total"]
theorem charLt_total (c1 c2 : HolChar) (h : ¬(c1 < c2) ∧ ¬(c2 < c1)) : c1 = c2 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.lt_def] at h
  omega

/-- HOL `CHR`: the character with the given code. Untagged infrastructure: HOL's
`CHR`/`ORD` are the canonical bijection between `num` and the 256 characters,
modelled here by `BitVec.ofNat 8`/`BitVec.toNat`. -/
def holChr (n : Nat) : HolChar := BitVec.ofNat 8 n

/-- HOL `ORD`: the code of a character. Untagged infrastructure (see `holChr`). -/
def holOrd (c : HolChar) : Nat := c.toNat

/-- Original `ORD_eq_0`: code zero is exactly the character `CHR 0`. -/
@[hol "cakeml/misc/miscScript.sml" "ORD_eq_0"]
theorem ord_eq_zero (c : HolChar) :
    (holOrd c = 0 ↔ c = holChr 0) ∧ (0 = holOrd c ↔ c = holChr 0) := by
  have hiff : holOrd c = 0 ↔ c = holChr 0 := by
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      simp only [holOrd] at h
      rw [holChr, BitVec.toNat_ofNat, h]
    · intro h
      rw [h, holOrd, holChr, BitVec.toNat_ofNat]
  exact ⟨hiff, by
    rw [eq_comm]
    exact hiff⟩

/-- Original `CHR_w2n_n2w_ORD`: `CHR`, `w2n`, `n2w` and `ORD` round-trip. -/
@[hol "cakeml/misc/miscScript.sml" "CHR_w2n_n2w_ORD"]
theorem chr_w2n_n2w_ord :
    (fun c : HolChar => holChr (BitVec.toNat (BitVec.ofNat 8 (holOrd c)))) = id := by
  funext c
  simp only [id_eq, holOrd, holChr]
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Original `n2w_ORD_CHR_w2n`: the other round-trip of the same four functions. -/
@[hol "cakeml/misc/miscScript.sml" "n2w_ORD_CHR_w2n"]
theorem n2w_ord_chr_w2n :
    (fun w : BitVec 8 => BitVec.ofNat 8 (holOrd (holChr (BitVec.toNat w)))) = id := by
  funext w
  have hlt : w.toNat < 2 ^ 8 := w.isLt
  simp only [id_eq, holOrd, holChr, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hlt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Original `CHR_w2n_n2w_ORD_simp`: the pointwise round-trip. -/
@[hol "cakeml/misc/miscScript.sml" "CHR_w2n_n2w_ORD_simp"]
theorem chr_w2n_n2w_ord_simp (c : HolChar) :
    holChr (BitVec.toNat (BitVec.ofNat 8 (holOrd c))) = c := by
  simp only [holOrd, holChr]
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Original `n2w_ORD_CHR_w2n_simp`: the pointwise round-trip. -/
@[hol "cakeml/misc/miscScript.sml" "n2w_ORD_CHR_w2n_simp"]
theorem n2w_ord_chr_w2n_simp (w : BitVec 8) :
    BitVec.ofNat 8 (holOrd (holChr (BitVec.toNat w))) = w := by
  have hlt : w.toNat < 2 ^ 8 := w.isLt
  simp only [holOrd, holChr, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hlt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Flapjack.Basis.Pure.MlString
