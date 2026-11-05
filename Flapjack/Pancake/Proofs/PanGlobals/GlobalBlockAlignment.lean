import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsGlobalBlockAlignment

/-- Flapjack arithmetic infrastructure: convert the reviewed byte-align fixed
point to divisibility at the dimensions allowed by the original state relation.
No single CakeML declaration has this synthesized statement. -/
private theorem aligned_mod {width : Nat} [NeZero width] (hw : goodDimindex width)
    (a : BitVec width) (ha : panGlobalsByteAlignedHOL a) :
    a.toNat % (width / 8) = 0 := by
  rcases hw with rfl | rfl
  · have h' : BitVec.ofNat 32 ((a.toNat / 4) * 4) = a := ha
    have hnat := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at hnat
    have hlt := a.isLt
    simp only [Nat.reduceDiv]
    omega
  · have h' : BitVec.ofNat 64 ((a.toNat / 8) * 8) = a := ha
    have hnat := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at hnat
    have hlt := a.isLt
    simp only [Nat.reduceDiv]
    omega

/-- Flapjack proof infrastructure for original Assign559-568: the global block
address is aligned when both the target top address and global offset are.
The original state relation already provides goodDimindex and both fixed points.
This combines HOL's external byte_aligned_add and aligned_add_sub_cor uses;
it is not a claimed generic port of either external library declaration. -/
theorem byteAligned_sub {width : Nat} [NeZero width]
    (a b : BitVec width) (hw : goodDimindex width)
    (ha : panGlobalsByteAlignedHOL a) (hb : panGlobalsByteAlignedHOL b) :
    panGlobalsByteAlignedHOL (a - b) := by
  have hma := aligned_mod hw a ha
  have hmb := aligned_mod hw b hb
  rcases hw with rfl | rfl
  · change BitVec.ofNat 32 (((a - b).toNat / 4) * 4) = a - b
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have hlt := (a - b).isLt
    have hmod : (a - b).toNat % 4 = 0 := by
      simp only [BitVec.toNat_sub]
      simp only [Nat.reduceDiv] at hma hmb
      omega
    omega
  · change BitVec.ofNat 64 (((a - b).toNat / 8) * 8) = a - b
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have hlt := (a - b).isLt
    have hmod : (a - b).toNat % 8 = 0 := by
      simp only [BitVec.toNat_sub]
      simp only [Nat.reduceDiv] at hma hmb
      omega
    omega

end Flapjack.PanGlobalsGlobalBlockAlignment
