import Flapjack.RiscV.L3.Step.LoadStep
import Flapjack.RiscV.L3.Defs.IntegerStore

/-! Evaluated original `riscv_stepScript.sml` memory-store instruction theorems
(`SD`/`SW`/`SH`/`SB`, lines 908-915) over the literal native `dfn'SD`/`dfn'SW`/
`dfn'SH`/`dfn'SB` equations.  Each write theorem keeps the original source
hypotheses captured from `riscv_stepTheory`: `mstatus.VM = 0w` for every store,
plus both architecture exclusions `ArchBase <> 0w` and `ArchBase <> 1w` for `SD`, plus the source `aligned`
condition (`SD` 3 bits, `SW` 2 bits, `SH` 1 bit).  `SB` has no alignment
condition.  The store factory is a plain `class` (not `class_rd0`), so no
generated `rd = 0w` companions exist.  The tagged right-hand sides state the original expanded `MEM8` updates.
The alignment premises justify reconstructing bytes from native word writes. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

/-- Untagged raw-result convenience equation used by the expanded source port. -/
theorem dfnSDRaw (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 3 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'SD» (rs1, rs2, offs) s =
      rawWriteData ((if rs1 = 0 then BitVec.signExtend 64 offs
        else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs), GPR rs2 s, 8) s := by
  simp only [«dfn'SD»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]

/-- Untagged raw-result convenience equation used by the expanded source port. -/
theorem dfnSWRaw (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 2 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'SW» (rs1, rs2, offs) s =
      rawWriteData ((if rs1 = 0 then BitVec.signExtend 64 offs
        else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs), GPR rs2 s, 4) s := by
  simp only [«dfn'SW»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]

/-- Untagged raw-result convenience equation used by the expanded source port. -/
theorem dfnSHRaw (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 1 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'SH» (rs1, rs2, offs) s =
      rawWriteData ((if rs1 = 0 then BitVec.signExtend 64 offs
        else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs), GPR rs2 s, 2) s := by
  simp only [«dfn'SH»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]

/-- Untagged raw-result convenience equation used by the expanded source port. -/
theorem dfnSBRaw (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'SB» (rs1, rs2, offs) s =
      rawWriteData ((if rs1 = 0 then BitVec.signExtend 64 offs
        else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs), GPR rs2 s, 1) s := by
  simp only [«dfn'SB»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]


theorem dfnSD (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (haligned : Flapjack.holAligned 3 (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true)
    : «dfn'SD» (rs1, rs2, offs) s =
      {s with MEM8 := holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 7#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 7#64) (if rs2 = 0 then 0#8 else holWordExtract 8 63 56 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 6#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 6#64) (if rs2 = 0 then 0#8 else holWordExtract 8 55 48 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 5#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 5#64) (if rs2 = 0 then 0#8 else holWordExtract 8 47 40 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 4#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 4#64) (if rs2 = 0 then 0#8 else holWordExtract 8 39 32 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 3#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 3#64) (if rs2 = 0 then 0#8 else holWordExtract 8 31 24 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 2#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 2#64) (if rs2 = 0 then 0#8 else holWordExtract 8 23 16 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 1#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 1#64) (if rs2 = 0 then 0#8 else holWordExtract 8 15 8 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) (if rs2 = 0 then 0#8 else holWordExtract 8 7 0 (s.c_gpr s.procID rs2)) (s.MEM8))))))))} := by
  rw [dfnSDRaw rs1 rs2 offs s harch0 harch hVM haligned]
  rw [ByteMemory.raw_write_expanded8 (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) (GPR rs2 s) s haligned]
  have e0 (v : BitVec 64) : v.extractLsb' 0 8 = holWordExtract 8 7 0 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e1 (v : BitVec 64) : v.extractLsb' 8 8 = holWordExtract 8 15 8 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e2 (v : BitVec 64) : v.extractLsb' 16 8 = holWordExtract 8 23 16 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e3 (v : BitVec 64) : v.extractLsb' 24 8 = holWordExtract 8 31 24 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e4 (v : BitVec 64) : v.extractLsb' 32 8 = holWordExtract 8 39 32 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e5 (v : BitVec 64) : v.extractLsb' 40 8 = holWordExtract 8 47 40 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e6 (v : BitVec 64) : v.extractLsb' 48 8 = holWordExtract 8 55 48 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e7 (v : BitVec 64) : v.extractLsb' 56 8 = holWordExtract 8 63 56 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [GPR, gpr, holWordExtract]

theorem dfnSW (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (haligned : Flapjack.holAligned 2 (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true)
    : «dfn'SW» (rs1, rs2, offs) s =
      {s with MEM8 := holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 3#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 3#64) (if rs2 = 0 then 0#8 else holWordExtract 8 31 24 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 2#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 2#64) (if rs2 = 0 then 0#8 else holWordExtract 8 23 16 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 1#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 1#64) (if rs2 = 0 then 0#8 else holWordExtract 8 15 8 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) (if rs2 = 0 then 0#8 else holWordExtract 8 7 0 (s.c_gpr s.procID rs2)) (s.MEM8))))} := by
  rw [dfnSWRaw rs1 rs2 offs s hVM haligned]
  rw [ByteMemory.raw_write_expanded4 (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) (GPR rs2 s) s haligned]
  have e0 (v : BitVec 64) : v.extractLsb' 0 8 = holWordExtract 8 7 0 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e1 (v : BitVec 64) : v.extractLsb' 8 8 = holWordExtract 8 15 8 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e2 (v : BitVec 64) : v.extractLsb' 16 8 = holWordExtract 8 23 16 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e3 (v : BitVec 64) : v.extractLsb' 24 8 = holWordExtract 8 31 24 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [GPR, gpr, holWordExtract]

theorem dfnSH (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (haligned : Flapjack.holAligned 1 (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true)
    : «dfn'SH» (rs1, rs2, offs) s =
      {s with MEM8 := holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs + 1#64 else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + 1#64) (if rs2 = 0 then 0#8 else holWordExtract 8 15 8 (s.c_gpr s.procID rs2)) (holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) (if rs2 = 0 then 0#8 else holWordExtract 8 7 0 (s.c_gpr s.procID rs2)) (s.MEM8))} := by
  rw [dfnSHRaw rs1 rs2 offs s hVM haligned]
  rw [ByteMemory.raw_write_expanded2 (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) (GPR rs2 s) s haligned]
  have e0 (v : BitVec 64) : v.extractLsb' 0 8 = holWordExtract 8 7 0 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have e1 (v : BitVec 64) : v.extractLsb' 8 8 = holWordExtract 8 15 8 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [GPR, gpr, holWordExtract]

theorem dfnSB (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    : «dfn'SB» (rs1, rs2, offs) s =
      {s with MEM8 := holUpdate (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) (if rs2 = 0 then 0#8 else holWordExtract 8 7 0 (s.c_gpr s.procID rs2)) (s.MEM8)} := by
  rw [dfnSBRaw rs1 rs2 offs s hVM]
  have haligned : Flapjack.holAligned 0 (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true := by
    rw [Flapjack.holAligned_iff]
    simp only [Nat.pow_zero]
    omega
  rw [ByteMemory.raw_write_expanded1 (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) (GPR rs2 s) s haligned]
  have e0 (v : BitVec 64) : v.extractLsb' 0 8 = holWordExtract 8 7 0 v := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [GPR, gpr, holWordExtract]

end Flapjack.RiscV.L3.Step
