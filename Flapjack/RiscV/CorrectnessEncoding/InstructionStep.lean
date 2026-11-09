module

public import Flapjack.RiscV.CorrectnessEncoding.Skip
public import Flapjack.RiscV.CorrectnessEncoding.Immediate
public import Flapjack.RiscV.CorrectnessEncoding.DecodeAddi
public import Flapjack.RiscV.CorrectnessEncoding.DecodeUpperImmediates
public import Flapjack.RiscV.L3.Defs.UpperJump

@[expose] public section

/-! Flapjack native instruction-step infrastructure. No separately named HOL
originals exist for these compositions. The internal write_next interface is
used only with proved literal Run equations; specialized instruction steps
below derive them and take no target-evaluation premise. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000


def writePost (ms : riscv_state) (r : BitVec 5) (v : BitVec 64) : riscv_state :=
  {ms with
    c_Skip := holUpdate ms.procID 4 ms.c_Skip
    c_gpr := holUpdate ms.procID (holUpdate r v (ms.c_gpr ms.procID)) ms.c_gpr
    c_PC := holUpdate ms.procID (ms.c_PC ms.procID + 4) ms.c_PC}

theorem write_post_rel (s : AsmState 64) (ms : riscv_state) (r : Nat)
    (v : BitVec 64) (bound : r < 32)
    (hr : targetStateRel riscvTarget s ms) :
    targetStateRel riscvTarget (updPc (s.pc + 4) (updReg r v s))
      (writePost ms (BitVec.ofNat 5 r) v) := by
  rcases hr with ⟨ok, pc, mem, regs, fp⟩
  have fields := (riscvOk_iff ms).mp ok
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (riscvOk_iff _).mpr
    simpa [writePost, holUpdate] using
      ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,
        aligned_add_four _ fields.2.2.2.2⟩
  · change (writePost ms (BitVec.ofNat 5 r) v).c_PC ms.procID = s.pc + 4
    change ms.c_PC ms.procID = s.pc at pc
    simp [writePost, holUpdate, pc]
  · exact mem
  · intro i hi
    have ibound : i < 32 := hi.1
    have ri := regs i hi
    change ms.c_gpr ms.procID (BitVec.ofNat 5 i) = s.regs i at ri
    change (writePost ms (BitVec.ofNat 5 r) v).c_gpr ms.procID (BitVec.ofNat 5 i) =
      (if i = r then v else s.regs i)
    by_cases eq : i = r
    · subst i
      simp [writePost, holUpdate]
    · have ne : BitVec.ofNat 5 r ≠ BitVec.ofNat 5 i := by
        intro e
        have n := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at n
        norm_num at n
        rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt ibound] at n
        exact eq n.symm
      simp [writePost, holUpdate, eq, ne, ri]
  · intro i hi
    change i < 0 at hi
    omega

theorem write_next (ms : riscv_state) (i : instruction) (w : BitVec 32)
    (r : BitVec 5) (v : BitVec 64) (rn : r ≠ 0#5)
    (ok : riscvOk ms = true) (decode : DecodeAny (.Word w) = i)
    (run : Run i {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (v,r) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip})
    (low0 : w.getLsbD 0 = true) (low1 : w.getLsbD 1 = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 w)
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 w)
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 w)
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 w) :
    NextRISCV ms = some (writePost ms r v) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  let written : riscv_state := {fetched with
    c_gpr := holUpdate ms.procID (holUpdate r v (ms.c_gpr ms.procID)) ms.c_gpr}
  have hf := encoded_fetch ms w fields.1 low0 low1 b0 b1 b2 b3
  have hr : Run i fetched = written := by
    rw [run]
    simp [«write'GPR», «write'gpr», fetched, written, rn]
  have hn := nextRISCV ms (.Word w) fetched i written
    ⟨hf, decode, hr, fields.2.2.2.1, fields.2.2.1⟩
  simpa [update_pc, «write'PC», Skip, fetched, written, writePost, holUpdate] using hn


/-- Literal low twelve bits of a signed 32-bit offset. -/
def low (c : BitVec 64) : BitVec 12 := RiscV.L3.holWordExtract 12 11 0 c
/-- Literal high twenty bits of the same offset, taken from the value with its
low twelve bits removed. -/
def high (c : BitVec 64) : BitVec 20 :=
  RiscV.L3.holWordExtract 20 31 12 (c - (low c).signExtend 64)
/-- Sign-extended high twenty bits above a zero low twelve. -/
def upperValue (c : BitVec 64) : BitVec 64 :=
  ((high c) ++ (0#12)).signExtend 64

theorem low_eq (c : BitVec 64) : low c = BitVec.extractLsb' 0 12 c := by
  apply BitVec.eq_of_toNat_eq
  simp [low, RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

theorem high_eq (c : BitVec 64) :
    high c = BitVec.extractLsb' 12 20 (c - (BitVec.extractLsb' 0 12 c).signExtend 64) := by
  rw [high, low_eq]
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

/-- Reconstruction from exactly the original signed offset guard; no additional
alignment or range premise is added. Shared by the Loc, far Jump and far Call
encodings. -/
theorem upperValue_add_low (c : BitVec 64)
    (range : -2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599)
    (aligned : c.toNat % 4 = 0) : upperValue c + (low c).signExtend 64 = c := by
  have zero : (BitVec.extractLsb' 0 2 c).setWidth 64 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, aligned]
  have bit : c.getLsbD 1 = false := by
    have e := congrArg (fun x : BitVec 64 => x.getLsbD 1) zero
    simpa using e
  have mask : (BitVec.extractLsb' 0 12 c) &&& ~~~(2 : BitVec 12) =
      BitVec.extractLsb' 0 12 c := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and]
    by_cases ei : i = 1
    · subst i
      rw [bit]
      rfl
    · have eb : (2 : BitVec 12).getLsbD i = false := by
        change Nat.testBit (2 ^ 1) i = false
        exact Nat.testBit_two_pow_of_ne (Ne.symm ei)
      rw [eb]
      simp only [Bool.not_false, Bool.and_true]
  have bounds : (0xFFFFFFFF80000000 : BitVec 64).sle c = true ∧
      c.sle 0x7FFFF7FF = true := by
    simp only [BitVec.sle_eq_decide, decide_eq_true_eq]
    change -2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599
    exact range
  have split := split_immediate_reconstruction c ⟨bounds.1,bounds.2,zero⟩
  have em : (-1 : BitVec 64) = (-1#64) := by decide
  rw [mask, em, ← BitVec.neg_eq_neg_one_mul, ← BitVec.sub_eq_add_neg] at split
  simpa [upperValue, high_eq, low_eq] using split

theorem auipc_low (r : BitVec 5) (c : BitVec 20) :
    (Encode (.ArithI (.AUIPC (r,c)))).getLsbD 0 = true ∧
      (Encode (.ArithI (.AUIPC (r,c)))).getLsbD 1 = true := by
  simp only [Encode, Utype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
  simp

theorem auipc_run (ms : riscv_state) (r : BitVec 5) (c : BitVec 64) :
    Run (.ArithI (.AUIPC (r,high c)))
      {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
    «write'GPR» (ms.c_PC ms.procID + upperValue c,r)
      {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
  simp [Run, «dfn'AUIPC», PC, upperValue]

/-- Actual AUIPC transition from emitted bytes and the source relation, shared
by the Loc, far Jump and far Call encodings; no separately named HOL original. -/
theorem auipc_step (s : AsmState 64) (ms : riscv_state)
    (r : Nat) (c : BitVec 64) (rn : BitVec.ofNat 5 r ≠ 0#5)
    (hr : targetStateRel riscvTarget s ms)
    (hb : bytesInMemoryHOL s.pc
      (riscvEncode (.ArithI (.AUIPC (BitVec.ofNat 5 r,high c)))) s.mem s.memDomain) :
    riscvTarget.next ms = writePost ms (BitVec.ofNat 5 r) (s.pc + upperValue c) := by
  have bytes := bytes_in_memory_thm () s ms _ _ _ _ ⟨hr, hb⟩
  have lowbits := auipc_low (BitVec.ofNat 5 r) (high c)
  have native := write_next ms (.ArithI (.AUIPC (BitVec.ofNat 5 r,high c)))
    (Encode (.ArithI (.AUIPC (BitVec.ofNat 5 r,high c))))
    (BitVec.ofNat 5 r) (ms.c_PC ms.procID + upperValue c) rn hr.1
    (decode_encode_auipc _ _) (auipc_run ms _ c) lowbits.1 lowbits.2
    bytes.2.2.2.2.2.1 bytes.2.2.2.2.2.2.1
    bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
  change holThe (NextRISCV ms) = _
  rw [native]
  have pc := hr.2.1
  change ms.c_PC ms.procID = s.pc at pc
  simp [pc, holThe]

end Flapjack.RiscV.TargetProof
