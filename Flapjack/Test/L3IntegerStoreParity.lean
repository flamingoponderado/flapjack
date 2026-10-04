import Flapjack.RiscV.L3.Defs.IntegerStore
set_option maxRecDepth 200000
namespace Flapjack.Test.L3IntegerStoreParity
open Flapjack.RiscV.L3
/-! Integer load/store regressions on physical memory. Original physical
register, byte, sign-extension, address-wrap and frame golden values are retained;
paging-only scenarios and TLB observations do not apply on riscv-mi. -/
private def fixture (base : riscv_state) (w b v o rd core arch vm : Nat) : riscv_state :=
  { base with procID := BitVec.ofNat 8 core, totalCore := 1, exception := .NoException, c_NextFetch := (fun _ => none), c_gpr := (fun _ reg => if reg = BitVec.ofNat 5 2 then BitVec.ofNat 64 b else if reg = BitVec.ofNat 5 3 then 81985529216486895 else 99),        c_MCSR := (fun id => { base.c_MCSR id with mstatus := { (base.c_MCSR id).mstatus with MMPRV := false, MPRV := 0, MPRV1 := 3, VM := BitVec.ofNat 5 vm }, mcpuid := { (base.c_MCSR id).mcpuid with ArchBase := BitVec.ofNat 2 arch } }),   MEM8 := (fun x => if (x - BitVec.ofNat 64 v).toNat < 8 then BitVec.ofNat 8 (w / 2 ^ (8 * (x - BitVec.ofNat 64 v).toNat)) else 0) }

private def trapView : Option TransferControl → Nat × Option Nat
  | some (.Trap t) => ((if t.trap == .Load_Fault then 1 else if t.trap == .Illegal_Instr then 2 else if t.trap == .AMO_Misaligned then 3 else if t.trap == .Store_AMO_Fault then 4 else 5),t.badaddr.map BitVec.toNat)
  | _ => (0,none)

private noncomputable def observation
    (f : (BitVec 5 × BitVec 5 × BitVec 12) → riscv_state → riscv_state)
    (s : riscv_state) (rs1 rs2 : BitVec 5) (offs : BitVec 12) (va : BitVec 64) := by
  classical
  exact
    let r := f (rs1,rs2,offs) s
    ((GPR rs2 r).toNat,(r.c_gpr s.procID rs2).toNat,(r.c_gpr (s.procID+1) rs2).toNat,
      trapView (r.c_NextFetch s.procID),r.exception == .NoException,
      (rawReadData 0 r).toNat,(rawReadData 8 r).toNat,(rawReadData va r).toNat,
      (List.range 8).map (fun i => (r.MEM8 (va+BitVec.ofNat 64 i)).toNat),

      decide ({ r with MEM8 := s.MEM8,  c_NextFetch := s.c_NextFetch, exception := s.exception } = s),
      r.totalCore,r.procID.toNat)

-- Original l3_integer_store_probe.out: sw_aligned.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_positive_memory.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 1311768465173141119 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,1311768467177459183,0,1311768467177459183,[239,205,171,137,120,86,52,18],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_rs2_zero.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758542507835392,0,18364758542507835392,[0,0,0,0,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_negative_offset_cross.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 8 7 4095 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17221764975064776704,71737338065693645,18364758544817573359,[239,205,171,137,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_offset_wrap.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 18446744073709551615 0 1 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_address_wrap.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 18446744073709551615 18446744073709551615 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 18446744073709551615) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,71737338065693645,0,18364758544817573359,[239,205,171,137,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_core_wrap.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 0 0 0 255 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],true,1,255) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_rv32_mode.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 0 0 0 7 0 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_rv128_mode.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 0 0 0 7 3 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_positive_offset.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 4 4 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4) (BitVec.ofNat 64 4) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,9920249030594527232,4275878552,18364758544817573359,[239,205,171,137,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_rs1_zero.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 99 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_aligned.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640588271,0,18364758546640588271,[239,205,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_positive_memory.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 1311768465173141119 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,1311768465173171695,0,1311768465173171695,[239,205,52,18,120,86,52,18],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_rs2_zero.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640535552,0,18364758546640535552,[0,0,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_negative_offset_cross.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 8 7 4095 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17221764975064776704,71737338072814797,18364758546640588271,[239,205,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_offset_wrap.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 18446744073709551615 0 1 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640588271,0,18364758546640588271,[239,205,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_address_wrap.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 18446744073709551615 18446744073709551615 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 18446744073709551615) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,71737338072814797,0,18364758546640588271,[239,205,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_positive_offset.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 0 4 4 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4) (BitVec.ofNat 64 4) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17750038457754845184,4275878552,18364758546640588271,[239,205,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_rs1_zero.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 99 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640588271,0,18364758546640588271,[239,205,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_aligned.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568559,0,18364758546640568559,[239,128,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_positive_memory.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 1311768465173141119 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,1311768465173141231,0,1311768465173141231,[239,86,52,18,120,86,52,18],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_rs2_zero.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568320,0,18364758546640568320,[0,128,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_negative_offset_cross.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 8 7 4095 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17221764975064776704,71737338072814720,18364758546640568559,[239,128,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_offset_wrap.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 18446744073709551615 0 1 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568559,0,18364758546640568559,[239,128,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_address_wrap.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 18446744073709551615 18446744073709551615 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 18446744073709551615) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,71737338072814720,0,18364758546640568559,[239,128,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_positive_offset.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 0 4 4 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4) (BitVec.ofNat 64 4) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17749953795359506432,4275878552,18364758546640568559,[239,128,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_rs1_zero.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 99 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568559,0,18364758546640568559,[239,128,84,246,152,186,220,254],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_aligned.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_positive_memory.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 1311768465173141119 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_rs2_zero.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_negative_offset_cross.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 8 7 4095 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17221764975064776704,320255973501901,81985529216486895,[239,205,171,137,103,69,35,1],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_offset_wrap.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 18446744073709551615 0 1 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_address_wrap.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 18446744073709551615 18446744073709551615 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 18446744073709551615) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,320255973501901,0,81985529216486895,[239,205,171,137,103,69,35,1],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_positive_offset.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 0 4 4 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4) (BitVec.ofNat 64 4) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,9920249030594527232,19088743,81985529216486895,[239,205,171,137,103,69,35,1],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_rs1_zero.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 99 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,rawWriteData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

end Flapjack.Test.L3IntegerStoreParity
