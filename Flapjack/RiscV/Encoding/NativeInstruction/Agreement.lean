module

public import Flapjack.RiscV.Encoding
public import Flapjack.RiscV.Encoding.Reference

@[expose] public section

/-! Unconditional production/native encoding agreement. These infrastructure
relations compare distinct Lean carriers and do not narrow the full tagged HOL
encoder. No target-run or operand-validity premise is introduced. -/
namespace Flapjack.RiscV

/-- Universal byte-order agreement for the full native instruction carrier.
This follows the existing Flapjack byte-slice theorem; it makes no claim about
production word encoding or cross-language equivalence. No HOL original names
this relation between the two Lean byte emitters, so it stays untagged. -/
theorem nativeEncodeBytes (i : L3.instruction) :
    encodeWordBytes (L3.Encode i) =
      Compiler.Encoders.RiscV.Target.riscvEncode i := by
  rw [encodeWordBytes_eq_extracts]
  simp only [Compiler.Encoders.RiscV.Target.riscvEncode, List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp [L3.holWordExtract, BitVec.extractLsb']

theorem encodeWordBytes_eq_weighted (value : BitVec 32) :
    encodeWordBytes value = EncodingReference.encodeWordBytesWeighted value := by
  simp only [encodeWordBytes, EncodingReference.encodeWordBytesWeighted,
    List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

end Flapjack.RiscV
