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

private theorem appendNumeric (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

private theorem rtypeNumeric (o : BitVec 7) (f3 : BitVec 3)
    (d a b : BitVec 5) (f7 : BitVec 7) :
    L3.Rtype (o,f3,d,a,b,f7) =
      BitVec.ofNat 32 (o.toNat + d.toNat * 128 + f3.toNat * 4096 +
        a.toNat * 32768 + b.toNat * 1048576 + f7.toNat * 33554432) := by
  apply BitVec.eq_of_toNat_eq
  change (f7 ++ (b ++ (a ++ (f3 ++ (d ++ o))))).toNat = _
  simp only [appendNumeric, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  omega

private theorem itypeNumeric (o : BitVec 7) (f3 : BitVec 3)
    (d a : BitVec 5) (i : BitVec 12) :
    L3.Itype (o,f3,d,a,i) =
      BitVec.ofNat 32 (o.toNat + d.toNat * 128 + f3.toNat * 4096 +
        a.toNat * 32768 + i.toNat * 1048576) := by
  apply BitVec.eq_of_toNat_eq
  change (i ++ (a ++ (f3 ++ (d ++ o)))).toNat = _
  simp only [appendNumeric, BitVec.toNat_ofNat, Nat.reducePow]
  omega

private theorem utypeNumeric (o : BitVec 7) (d : BitVec 5) (i : BitVec 20) :
    L3.Utype (o,d,i) =
      BitVec.ofNat 32 (o.toNat + d.toNat * 128 + i.toNat * 4096) := by
  apply BitVec.eq_of_toNat_eq
  change (i ++ (d ++ o)).toNat = _
  simp only [appendNumeric, BitVec.toNat_ofNat, Nat.reducePow]
  omega

private theorem stypeNumeric (o : BitVec 7) (f3 : BitVec 3)
    (a b : BitVec 5) (i : BitVec 12) :
    L3.Stype (o,f3,a,b,i) =
      BitVec.ofNat 32 (o.toNat + (i.toNat / 32 % 128) * 33554432 +
        b.toNat * 1048576 + a.toNat * 32768 + f3.toNat * 4096 +
        (i.toNat % 32) * 128) := by
  apply BitVec.eq_of_toNat_eq
  change ((L3.holWordExtract 7 11 5 i) ++
    (b ++ (a ++ (f3 ++ ((L3.holWordExtract 5 4 0 i) ++ o))))).toNat = _
  simp only [appendNumeric, BitVec.toNat_ofNat, Nat.reducePow]
  simp [L3.holWordExtract, Nat.shiftRight_eq_div_pow]
  omega

private theorem singletonV2w (b : Bool) : L3.holV2w 1 [b] = BitVec.ofBool b := by
  cases b <;> decide

private theorem bitNumeric (w : BitVec m) (n : Nat) :
    (L3.holV2w 1 [w.getLsbD n]).toNat = w.toNat / 2 ^ n % 2 := by
  rw [singletonV2w, BitVec.toNat_ofBool]
  by_cases h : w.toNat / 2 ^ n % 2 = 1
  · simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, h]
  · simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, h]
    omega

private theorem sbtypeNumeric (o : BitVec 7) (f3 : BitVec 3)
    (a b : BitVec 5) (i : BitVec 12) :
    L3.SBtype (o,f3,a,b,i) =
      BitVec.ofNat 32 (o.toNat + (i.toNat / 2048 % 2) * 2147483648 +
        (i.toNat / 16 % 64) * 33554432 + b.toNat * 1048576 +
        a.toNat * 32768 + f3.toNat * 4096 + (i.toNat % 16) * 256 +
        (i.toNat / 1024 % 2) * 128) := by
  apply BitVec.eq_of_toNat_eq
  change ((L3.holV2w 1 [i.getLsbD 11]) ++
    ((L3.holWordExtract 6 9 4 i) ++ (b ++ (a ++ (f3 ++
      ((L3.holWordExtract 4 3 0 i) ++ ((L3.holV2w 1 [i.getLsbD 10]) ++ o))))))).toNat = _
  simp only [appendNumeric, bitNumeric, BitVec.toNat_ofNat, Nat.reducePow]
  simp [L3.holWordExtract, Nat.shiftRight_eq_div_pow]
  omega

private theorem ujtypeNumeric (o : BitVec 7) (d : BitVec 5) (i : BitVec 20) :
    L3.UJtype (o,d,i) =
      BitVec.ofNat 32 (o.toNat + d.toNat * 128 +
        (i.toNat / 2048 % 256) * 4096 + (i.toNat / 1024 % 2) * 1048576 +
        (i.toNat % 1024) * 2097152 + (i.toNat / 524288 % 2) * 2147483648) := by
  apply BitVec.eq_of_toNat_eq
  change ((L3.holV2w 1 [i.getLsbD 19]) ++
    ((L3.holWordExtract 10 9 0 i) ++ ((L3.holV2w 1 [i.getLsbD 10]) ++
      ((L3.holWordExtract 8 18 11 i) ++ (d ++ o))))).toNat = _
  simp only [appendNumeric, bitNumeric, BitVec.toNat_ofNat, Nat.reducePow]
  simp [L3.holWordExtract, Nat.shiftRight_eq_div_pow]
  omega

theorem encodeWordBytes_eq_weighted (value : BitVec 32) :
    encodeWordBytes value = EncodingReference.encodeWordBytesWeighted value := by
  simp only [encodeWordBytes, EncodingReference.encodeWordBytesWeighted,
    List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

end Flapjack.RiscV
