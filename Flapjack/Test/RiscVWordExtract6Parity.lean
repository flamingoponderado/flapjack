import Flapjack.RiscV.CorrectnessEncoding

/-! The checked HOL oracle values are in
    `scripts/hol-probes/riscv_word_extract_6_probe.out`.  These guards pin the
    zero and largest in-range boundary cases for
    `riscv_targetProof$word_extract_6`. -/

namespace Flapjack.Test.RiscVWordExtract6Parity

open Flapjack.RiscV

def zeroGuard : Bool :=
  decide (BitVec.extractLsb' 0 6 (0 : BitVec 64) =
    BitVec.setWidth 6 (0 : BitVec 64))

def maxInRangeGuard : Bool :=
  decide (BitVec.extractLsb' 0 6 (63 : BitVec 64) =
    BitVec.setWidth 6 (63 : BitVec 64))

example : BitVec.extractLsb' 0 6 (0 : BitVec 64) =
    BitVec.setWidth 6 (0 : BitVec 64) :=
  wordExtract6OfLt64 0 (by decide)

example : BitVec.extractLsb' 0 6 (63 : BitVec 64) =
    BitVec.setWidth 6 (63 : BitVec 64) :=
  wordExtract6OfLt64 63 (by decide)

-- Full native arithmetic theorem consumers; the HOL probe replays universal
-- original proofs rather than selecting these applications as an oracle.
example (c : BitVec 64) (h : Flapjack.holAligned 2 c = true) : c.getLsbD 1 = false :=
  TargetProof.aligned_bit_one c h

example (b x y : Bool) :
    ((if b then (1 : BitVec 64) else 0) =
      (L3.holV2w 64 [x] ||| L3.holV2w 64 [y])) ↔ b = (x || y) :=
  TargetProof.singleton_or b x y

example (a b : BitVec 64) :
    (18446744073709551616 ≤ a.toNat + (b.toNat + 1) ↔
      (18446744073709551616 : BitVec 65).ule (a.setWidth 65 + b.setWidth 65 + 1) = true) :=
  (TargetProof.carry_widen a b).1

example (a b : BitVec 64) :
    (18446744073709551616 ≤ a.toNat + b.toNat ↔
      (18446744073709551616 : BitVec 65).ule (a.setWidth 65 + b.setWidth 65) = true) :=
  (TargetProof.carry_widen a b).2

example (a b : BitVec 64) :
    BitVec.ofNat 64 ((a.toNat * b.toNat) / 18446744073709551616) =
      BitVec.extractLsb' 64 64 (a.setWidth 128 * b.setWidth 128) :=
  TargetProof.mul_long a b

example (w : BitVec 64) (n : Nat) (h : n < 64) :
    ((w <<< (64 - n)) ||| (w >>> n)) = w.rotateRight n :=
  TargetProof.ror w n h

#guard zeroGuard
#guard maxInRangeGuard
#guard zeroGuard && maxInRangeGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("word_extract_6 at zero", zeroGuard),
      ("word_extract_6 at 63", maxInRangeGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVWordExtract6Parity
