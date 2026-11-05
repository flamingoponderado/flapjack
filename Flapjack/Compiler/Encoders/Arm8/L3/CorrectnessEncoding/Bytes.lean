import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Skip
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 4000000

/-!
# L3 ARMv8 byte-walk infrastructure for the encoder-correctness cases

The four bytes `arm8Encode` emits for a 32-bit word are read back by the
rendered `Mem` as that word, so every `encoder_correct` case can start from
`Fetch` on the emitted bytes.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm

/-- The rendered `Mem` reassembles the four little-endian bytes of a word. -/
theorem holV2w_word_bytes (w : BitVec 32) :
    holV2w 32
      (holW2v (BitVec.ofNat 8 ((w >>> 24).toNat)) ++
        (holW2v (BitVec.ofNat 8 ((w >>> 16).toNat)) ++
          (holW2v (BitVec.ofNat 8 ((w >>> 8).toNat)) ++
            holW2v (BitVec.ofNat 8 ((w >>> 0).toNat))))) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Flapjack.RiscV.L3.holV2w, holW2v, List.length_append, List.length_map,
    List.length_range]
  rw [Flapjack.getLsbD_holFcpWord]
  simp only [hi, decide_true, Bool.true_and]
  interval_cases i <;>
    simp [List.getD_eq_getElem?_getD, BitVec.getLsbD_ofNat,
      BitVec.getElem_eq_testBit_toNat]

/-- `Mem` reads the four emitted little-endian bytes of `w` and returns `w`
without changing the state. -/
theorem arm8Mem_word (ms : arm8_state) (w : BitVec 32)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 32) (ms.PC, (4, AccType.AccType_IFETCH)) ms = (w, ms) := by
  simp only [Mem]
  simp [holFor]
  constructor
  · rw [CheckAlignment_aligned ms ms.PC 4 AccType.AccType_IFETCH false hal]
    rw [BigEndian_false ms hel he0]
    simp only [Bool.false_eq_true, if_false, BitVec.ofNat_eq_ofNat] at *
    rw [h0, h1, h2, h3]
    simpa using holV2w_word_bytes w
  · exact CheckAlignment_aligned ms ms.PC 4 AccType.AccType_IFETCH false hal

/-- `Fetch` reads the four emitted bytes of `w`. -/
theorem arm8Fetch_word (ms : arm8_state) (w : BitVec 32)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Fetch ms = (w, ms) := by
  simp only [Fetch]
  exact arm8Mem_word ms w h0 h1 h2 h3 hal he0 hel

/-- One `NextStateARM8` step on a state holding the encoded word of a
non-branch instruction runs that instruction and advances the PC by four. -/
theorem arm8Next_word (ms : arm8_state) (w : BitVec 32) (i : instruction)
    (hdec : Decode w = i)
    (hbr : (Run i { ms with branch_hint := none }).branch_hint = none)
    (hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    NextStateARM8 ms = some { (Run i { ms with branch_hint := none }) with
      PC := (Run i { ms with branch_hint := none }).PC + 4 } := by
  have hfetch : Fetch { ms with branch_hint := none } = (w, { ms with branch_hint := none }) :=
    arm8Fetch_word { ms with branch_hint := none } w h0 h1 h2 h3 hal he0 hel
  simp only [NextStateARM8, Next]
  rw [hfetch]
  simp only [hdec]
  rw [hbr]
  simp only [Option.isSome_none, Bool.not_false, if_true]
  rw [hexc]
  simp

/-- `arm8Next` of a state holding the encoded word of a non-branch
instruction, as an equation with any state `T` that the run of the
instruction, with the PC advanced by four, equals (Flapjack infrastructure for
the non-branch `arm8Next_*` step equations; branch steps such as
`arm8Next_branchConditional` change the PC differently and are not
instances). -/
theorem arm8Next_eq (ms : arm8_state) (w : BitVec 32) (i : instruction) (T : arm8_state)
    (hdec : Decode w = i)
    (hT : { (Run i { ms with branch_hint := none }) with
      PC := (Run i { ms with branch_hint := none }).PC + 4 } = T)
    (hbr : T.branch_hint = none) (hexc : T.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms = T := by
  have hbr' : (Run i { ms with branch_hint := none }).branch_hint = none :=
    (congrArg (fun x : arm8_state => x.branch_hint) hT).trans hbr
  have hexc' : (Run i { ms with branch_hint := none }).exception = exception.NoException :=
    (congrArg (fun x : arm8_state => x.exception) hT).trans hexc
  unfold arm8Next
  rw [arm8Next_word ms w i hdec hbr' hexc' h0 h1 h2 h3 hal he0 hel, hT]
  rfl

end Flapjack.Compiler.Encoders.Arm8.L3
