module

public import Flapjack.RiscV.CorrectnessEncoding.Length
public import Flapjack.RiscV.CorrectnessEncoding.BytesInMemory
public import Flapjack.RiscV.CorrectnessEncoding.Arithmetic

@[expose] public section

/-!
Port of `riscv_targetProofScript.sml`, the correctness of the RISC-V encoder
`riscvEnc` against the L3 model. The `riscv_encoder_correct` cases live in the
submodules under `Flapjack/RiscV/CorrectnessEncoding/`.
-/
namespace Flapjack.RiscV

/-! HOL `riscv_targetProof$word_extract_6` states that when a 64-bit word is
    below 64, its low six-bit slice equals its 6-bit truncation (`w2w`).  HOL
    unsigned `<+` is the `toNat` bound here, slicing `(5 >< 0)` is extraction
    from bit 0 with length 6, and `w2w` retains the low six bits. -/
@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "word_extract_6"]
theorem wordExtract6OfLt64 (word : BitVec 64) (_hword : word.toNat < 64) :
    BitVec.extractLsb' 0 6 word = BitVec.setWidth 6 word := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb', Nat.shiftRight_zero, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth]

end Flapjack.RiscV
