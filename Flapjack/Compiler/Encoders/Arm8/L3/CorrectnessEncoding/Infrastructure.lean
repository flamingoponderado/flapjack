import Flapjack.Compiler.Encoders.Arm8.L3.Target.State
import Flapjack.Misc.BytesInMemory
import Flapjack.Compiler.Encoders.Arm8.BitVecLemmas
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect

/-!
# Shared infrastructure for the L3 ARMv8 encoder-correctness cases

Byte-walk lemmas, the `Aligned`/`holAligned` bridge, and validity/post-relation
invariance facts reused by the `encoder_correct arm8TargetL3` case split.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The `j`-th byte of a byte list in memory, for every `j` below the length. -/
theorem bytesInMemoryHOL_get {width : Nat} [NeZero width]
    {a : BitVec width} {bs : List (BitVec 8)} {m : BitVec width → BitVec 8}
    {d : BitVec width → Prop} (h : bytesInMemoryHOL a bs m d) :
    ∀ j, j < bs.length → m (a + BitVec.ofNat width j) = bs.getD j 0 := by
  revert h
  induction bs generalizing a with
  | nil => intro _ j hj; simp at hj
  | cons x xs ih =>
      intro h j hj
      obtain ⟨hx, hd, ht⟩ := h
      cases j with
      | zero => simpa using hx
      | succ j =>
          have hj' : j < xs.length := by simpa using hj
          have hrec := ih ht j hj'
          rw [← addOneOffset]
          simpa using hrec

/-- `Aligned` at size four is plain 4-byte alignment (`pc.toNat % 4 = 0`),
which is what `arm8_ok`'s `aligned 2` requires (Flapjack infrastructure; HOL
`arm8_ok` uses `aligned 2`). -/
theorem Aligned_four_iff (pc : BitVec 64) :
    Aligned (TN := 64) (pc, 4) = true ↔ pc.toNat % 4 = 0 := by
  simp only [Aligned, Align, beq_iff_eq]
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    have hle : 4 * (pc.toNat / 4) ≤ pc.toNat := by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle pc.isLt)] at ht
    rw [ht]
    exact Nat.mul_mod_right 4 (pc.toNat / 4)
  · intro h
    apply BitVec.eq_of_toNat_eq
    have hle : 4 * (pc.toNat / 4) ≤ pc.toNat := by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle pc.isLt),
      Nat.mul_comm 4 (pc.toNat / 4), Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)]

/-- `arm8_ok` does not read the register file, so setting one register keeps
the validity gate. -/
theorem arm8Ok_setReg (ms : arm8_state) (r : BitVec 5) (v : BitVec 64)
    (h : arm8Ok ms = true) :
    arm8Ok { ms with REG := fun x => if x = r then v else ms.REG x } = true := by
  rw [arm8Ok_iff] at h ⊢
  exact h

/-- `arm8_ok` reads the PC only through `aligned 2`. -/
theorem arm8Ok_setPc (ms : arm8_state) (pc : BitVec 64)
    (h : arm8Ok ms = true) (hal : holAligned 2 pc = true) :
    arm8Ok { ms with PC := pc } = true := by
  rw [arm8Ok_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, hal⟩

/-- The target-state relation is unchanged when only the source PC moves to
the machine PC. -/
theorem targetStateRel_updPc (s : AsmState 64) (ms : arm8_state) (pc : BitVec 64)
    (h : targetStateRel arm8TargetL3 s ms) (hpc : ms.PC = pc) :
    targetStateRel arm8TargetL3 (updPc pc s) ms := by
  obtain ⟨hok, hp, hmem, hreg, hfp⟩ := h
  rw [arm8TargetL3_getPc] at hp
  refine ⟨hok, ?_, ?_, ?_, ?_⟩
  · simp only [arm8TargetL3_getPc, updPc]
    exact hpc
  · intro a ha
    exact hmem a ha
  · intro i hi
    exact hreg i hi
  · intro i hi
    exact hfp i hi

end Flapjack.Compiler.Encoders.Arm8.L3
