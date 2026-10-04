import Flapjack.RiscV.L3.Defs.IntegerLoad
set_option maxRecDepth 200000
set_option maxErrors 5
namespace Flapjack.Test.L3IntegerLoadParity
open Flapjack.RiscV.L3

/-! Integer load/store regressions on physical memory. Original physical
register, byte, sign-extension, address-wrap and frame golden values are retained;
paging-only scenarios and TLB observations do not apply on riscv-mi. -/

private theorem lwShape (s : riscv_state) (rd rs : BitVec 5) (offs : BitVec 12) :
    «dfn'LW» (rd,rs,offs) s =
    let v := GPR rs s + BitVec.signExtend 64 offs
    let (addr,t) := translateAddr (v,fetchType.Data,accessType.Read) s
    match addr with
    | none => signalAddressException (ExceptionType.Load_Fault,v) t
    | some p => «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t)),rd) t := by
  rfl

private theorem lwuShape (s : riscv_state) (rd rs : BitVec 5) (offs : BitVec 12) :
    «dfn'LWU» (rd,rs,offs) s =
    let (is32,s) := in32BitMode () s
    if is32 then signalException ExceptionType.Illegal_Instr s else
    let v := GPR rs s + BitVec.signExtend 64 offs
    let (addr,t) := translateAddr (v,fetchType.Data,accessType.Read) s
    match addr with
    | none => signalAddressException (ExceptionType.Load_Fault,v) t
    | some p => «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 31 0 (rawReadData p t)),rd) t := by
  rfl

private theorem lhShape (s : riscv_state) (rd rs : BitVec 5) (offs : BitVec 12) :
    «dfn'LH» (rd,rs,offs) s =
    let v := GPR rs s + BitVec.signExtend 64 offs
    let (addr,t) := translateAddr (v,fetchType.Data,accessType.Read) s
    match addr with
    | none => signalAddressException (ExceptionType.Load_Fault,v) t
    | some p => «write'GPR» (BitVec.signExtend 64 (holWordExtract 16 15 0 (rawReadData p t)),rd) t := by
  rfl

private theorem lhuShape (s : riscv_state) (rd rs : BitVec 5) (offs : BitVec 12) :
    «dfn'LHU» (rd,rs,offs) s =
    let v := GPR rs s + BitVec.signExtend 64 offs
    let (addr,t) := translateAddr (v,fetchType.Data,accessType.Read) s
    match addr with
    | none => signalAddressException (ExceptionType.Load_Fault,v) t
    | some p => «write'GPR» (BitVec.setWidth 64 (holWordExtract 16 15 0 (rawReadData p t)),rd) t := by
  rfl

private theorem lbShape (s : riscv_state) (rd rs : BitVec 5) (offs : BitVec 12) :
    «dfn'LB» (rd,rs,offs) s =
    let v := GPR rs s + BitVec.signExtend 64 offs
    let (addr,t) := translateAddr (v,fetchType.Data,accessType.Read) s
    match addr with
    | none => signalAddressException (ExceptionType.Load_Fault,v) t
    | some p => «write'GPR» (BitVec.signExtend 64 (holWordExtract 8 7 0 (rawReadData p t)),rd) t := by
  rfl

private theorem lbuShape (s : riscv_state) (rd rs : BitVec 5) (offs : BitVec 12) :
    «dfn'LBU» (rd,rs,offs) s =
    let v := GPR rs s + BitVec.signExtend 64 offs
    let (addr,t) := translateAddr (v,fetchType.Data,accessType.Read) s
    match addr with
    | none => signalAddressException (ExceptionType.Load_Fault,v) t
    | some p => «write'GPR» (BitVec.setWidth 64 (holWordExtract 8 7 0 (rawReadData p t)),rd) t := by
  rfl

private theorem ldShape (s : riscv_state) (rd rs : BitVec 5) (offs : BitVec 12) :
    «dfn'LD» (rd,rs,offs) s =
    let (is32,s) := in32BitMode () s
    if is32 then signalException ExceptionType.Illegal_Instr s else
    let v := GPR rs s + BitVec.signExtend 64 offs
    let (addr,t) := translateAddr (v,fetchType.Data,accessType.Read) s
    match addr with
    | none => signalAddressException (ExceptionType.Load_Fault,v) t
    | some p => «write'GPR» (rawReadData p t,rd) t := by
  rfl

private def fixture (base : riscv_state) (w b v o rd core arch vm : Nat) : riscv_state :=
  { base with procID := BitVec.ofNat 8 core, totalCore := 1, exception := .NoException, c_NextFetch := (fun _ => none), c_gpr := (fun _ reg => if reg = BitVec.ofNat 5 2 then BitVec.ofNat 64 b else 99),        c_MCSR := (fun id => { base.c_MCSR id with mstatus := { (base.c_MCSR id).mstatus with MMPRV := false, MPRV := 0, MPRV1 := 3, VM := BitVec.ofNat 5 vm }, mcpuid := { (base.c_MCSR id).mcpuid with ArchBase := BitVec.ofNat 2 arch } }),         MEM8 := (fun x => if (x - BitVec.ofNat 64 v).toNat < 8 then BitVec.ofNat 8 (w / 2 ^ (8 * (x - BitVec.ofNat 64 v).toNat)) else 0) }

private def trapView : Option TransferControl → Nat × Option Nat
  | some (.Trap t) => ((if t.trap == .Load_Fault then 1 else if t.trap == .Illegal_Instr then 2 else 3),t.badaddr.map BitVec.toNat)
  | _ => (0,none)

private noncomputable def observation
    (f : (BitVec 5 × BitVec 5 × BitVec 12) → riscv_state → riscv_state)
    (s : riscv_state) (rd : BitVec 5) (offs : BitVec 12) (va : BitVec 64) := by
  classical
  exact
    let r := f (rd,2,offs) s
    ((GPR rd r).toNat,(r.c_gpr s.procID rd).toNat,(r.c_gpr (s.procID+1) rd).toNat,
      trapView (r.c_NextFetch s.procID),r.exception == .NoException,
      (rawReadData 0 r).toNat,(r.MEM8 va).toNat,

      decide ({ r with MEM8 := s.MEM8, c_gpr := s.c_gpr,  c_NextFetch := s.c_NextFetch, exception := s.exception } = s),
      r.totalCore,r.procID.toNat)

-- Original l3_integer_load_probe.out: lw_negative.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lw_positive.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (305419903,305419903,99,(0,none),true,1311768465173141119,127,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lw_rd_zero.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lw_unaligned.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,9223372036854775808,128,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lw_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_negative.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (4132733056,4132733056,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_positive.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (305419903,305419903,99,(0,none),true,1311768465173141119,127,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_rd_zero.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_unaligned.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (4132733056,4132733056,99,(0,none),true,9223372036854775808,128,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (4132733056,4132733056,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_negative.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18446744073709518976,18446744073709518976,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_positive.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (22143,22143,99,(0,none),true,1311768465173141119,127,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_rd_zero.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_unaligned.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (18446744073709518976,18446744073709518976,99,(0,none),true,9223372036854775808,128,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (18446744073709518976,18446744073709518976,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_negative.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (32896,32896,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_positive.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (22143,22143,99,(0,none),true,1311768465173141119,127,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_rd_zero.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_unaligned.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (32896,32896,99,(0,none),true,9223372036854775808,128,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (32896,32896,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_negative.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18446744073709551488,18446744073709551488,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_positive.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (127,127,99,(0,none),true,1311768465173141119,127,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_rd_zero.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_unaligned.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (18446744073709551488,18446744073709551488,99,(0,none),true,9223372036854775808,128,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (18446744073709551488,18446744073709551488,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_negative.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (128,128,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_positive.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (127,127,99,(0,none),true,1311768465173141119,127,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_rd_zero.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_unaligned.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (128,128,99,(0,none),true,9223372036854775808,128,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (128,128,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_negative.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_positive.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (1311768465173141119,1311768465173141119,99,(0,none),true,1311768465173141119,127,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_rd_zero.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_unaligned.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (18364758546640568448,18364758546640568448,99,(0,none),true,9223372036854775808,128,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_core_wrap.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 0 0 0 1 255 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,99,(0,none),true,18364758546640568448,128,true,1,255) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_rv32_mode.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 0 0 0 1 7 0 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (99,99,99,(2,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_rv128_mode.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 0 0 0 1 7 3 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,99,(0,none),true,18364758546640568448,128,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,
    rawReadData,MEM,«write'MEM»,
    holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


end Flapjack.Test.L3IntegerLoadParity
