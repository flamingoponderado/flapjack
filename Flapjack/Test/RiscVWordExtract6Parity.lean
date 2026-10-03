import Flapjack.RiscV.CorrectnessEncoding

/-! The checked HOL oracle values are in
    `scripts/hol-probes/riscv_word_extract_6_probe.out`.  These guards pin the
    zero and largest in-range boundary cases for
    `riscv_targetProof$word_extract_6`. -/

namespace Flapjack.Test.NativeBytesConsumers
open Flapjack RiscV.L3 Compiler.Encoders.RiscV.Target Compiler.Encoders.Asm

example {α : Type} (_w : α) (s : AsmState 64) (state : riscv_state)
    (a b c d : BitVec 8)
    (h : targetStateRel riscvTarget s state ∧
      bytesInMemoryHOL (s.pc) [a,b,c,d] s.mem s.memDomain) :
    state.exception = exception.NoException ∧
    (state.c_MCSR state.procID).mstatus.VM = 0 ∧
    (state.c_MCSR state.procID).mcpuid.ArchBase = 2 ∧
    state.c_NextFetch state.procID = none ∧
    holAligned 2 (state.c_PC state.procID) = true ∧
    state.MEM8 (state.c_PC state.procID) = a ∧
    state.MEM8 (state.c_PC state.procID + 1) = b ∧
    state.MEM8 (state.c_PC state.procID + 2) = c ∧
    state.MEM8 (state.c_PC state.procID + 3) = d ∧
    s.memDomain (state.c_PC state.procID + 3) ∧
    s.memDomain (state.c_PC state.procID + 2) ∧
    s.memDomain (state.c_PC state.procID + 1) ∧
    s.memDomain (state.c_PC state.procID) :=
  RiscV.TargetProof.bytes_in_memory_thm _w s state a b c d h

example (w : BitVec 64) (s : AsmState 64) (state : riscv_state)
    (a b c d : BitVec 8)
    (h : targetStateRel riscvTarget s state ∧
      bytesInMemoryHOL (s.pc + w) [a,b,c,d] s.mem s.memDomain) :
    state.MEM8 (state.c_PC state.procID + w) = a ∧
    state.MEM8 (state.c_PC state.procID + w + 1) = b ∧
    state.MEM8 (state.c_PC state.procID + w + 2) = c ∧
    state.MEM8 (state.c_PC state.procID + w + 3) = d ∧
    s.memDomain (state.c_PC state.procID + w + 3) ∧
    s.memDomain (state.c_PC state.procID + w + 2) ∧
    s.memDomain (state.c_PC state.procID + w + 1) ∧
    s.memDomain (state.c_PC state.procID + w) :=
  RiscV.TargetProof.bytes_in_memory_thm2 w s state a b c d h

example
    (env : Nat → riscv_state → riscv_state) (a : BitVec 64)
    (xs : List (BitVec 8)) (m : BitVec 64 → BitVec 8) (dm : BitVec 64 → Prop)
    (h : bytesInMemoryHOL a xs m dm ∧
      ∀ (i : Nat) (ms' : riscv_state), ∀ address, dm address →
        (env i ms').MEM8 address = ms'.MEM8 address) :
    ∀ (i : Nat) (ms' : riscv_state), ∀ pc,
      pc ∈ Compiler.Encoders.AsmProps.allPcs xs.length a 0 →
        (env i ms').MEM8 pc = ms'.MEM8 pc :=
  RiscV.TargetProof.bytes_in_memory_IMP_all_pcs_MEM8 env a xs m dm h

example (i : instruction) : (riscvEncode i).length = 4 :=
  RiscV.TargetProof.length_riscv_encode i

example (i : instruction) : riscvEncode i ≠ [] :=
  RiscV.TargetProof.riscv_encode_not_nil i

example (i : HolAsm 64) :
    (riscvEnc i).length % 4 = 0 ∧ riscvEnc i ≠ [] :=
  RiscV.TargetProof.riscv_encoding i

end Flapjack.Test.NativeBytesConsumers

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

example (c : BitVec 64) :
    ((BitVec.extractLsb' 0 32 c).getLsbD 11 = c.getLsbD 11) ∧
    ((BitVec.extractLsb' 32 32 c).getLsbD 11 = c.getLsbD 43) ∧
    ((~~~(BitVec.extractLsb' 32 32 c)).getLsbD 11 = !(c.getLsbD 43)) :=
  TargetProof.slice_bit_eleven c

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
