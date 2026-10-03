import Flapjack.RiscV.L3.Defs.IntegerLoad
set_option maxRecDepth 200000
set_option maxErrors 5
namespace Flapjack.Test.L3IntegerLoadParity
open Flapjack.RiscV.L3

/-! Flapjack regressions, no standalone HOL originals. The unconditional
whole-state normal forms retain every original branch and returned MMU state,
including unspecified architecture/VM results. Numeric fixtures keep arbitrary
unrelated native fields and replay original captures; they are not full pass or
runtime correctness theorems. -/

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

-- Flapjack-specific width-one word normalization; no standalone HOL original.
-- Keeping this checked fact opaque avoids carrying generic FCP cast proofs
-- through the page-walk observations.
private theorem singletonWord (b : Bool) :
    holV2w 1 [b] = (if b then (1 : BitVec 1) else 0) := by
  cases b <;> decide

-- Flapjack regression normalization for the complete aligned PTE word store.
-- No standalone HOL original; the original rawWriteData equation is unchanged.
private theorem writeFullWord (w : BitVec 64) (s : riscv_state) :
    rawWriteData (BitVec.ofNat 64 0, w, 8) s = «write'MEM» (w, BitVec.ofNat 61 0) s := by
  have hmask : ((BitVec.setWidth 64 (BitVec.ofNat 1 1) <<< (8 * 8)) -
      (BitVec.ofNat 64 1)) = BitVec.allOnes 64 := by decide
  have hidx : holWordExtract 61 63 3 (BitVec.ofNat 64 0) = BitVec.ofNat 61 0 := by decide
  have halign : holWordExtract 3 2 0 (BitVec.ofNat 64 0) = BitVec.ofNat 3 0 := by decide
  simp only [rawWriteData, hmask, hidx, halign]
  simp only [BitVec.toNat_zero, BEq.refl, Bool.true_eq, ↓reduceIte,
    BitVec.not_allOnes, BitVec.and_zero, BitVec.and_allOnes, BitVec.zero_or]

-- Flapjack-specific empty-table normalizations, with no standalone HOL originals.
-- Both retain arbitrary original parameters and the complete native state.
private theorem lookupEmpty (asid : BitVec 6) (va : BitVec 64) :
    lookupTLB (asid, va, fun _ => none) = none := by
  simp [lookupTLB, TLBEntries, Flapjack.holFor]

private theorem insertEmpty (asid : BitVec 6) (va pa pteAddr : BitVec 64)
    (pte : SV_PTE) (level : Nat) (global : Bool) (s : riscv_state) :
    addToTLB (asid, va, pa, pte, pteAddr, level, global, fun _ => none) s =
      holUpdate (BitVec.ofNat 4 0)
        (some (mkTLBEntry (asid, global, va, pa, pte, level, pteAddr) s))
        (fun _ => none) := by
  simp [addToTLB, TLBEntries, Flapjack.holFor, holUpdate]


private def fixture (base : riscv_state) (w b v o rd core arch vm : Nat) : riscv_state :=
  { base with procID := BitVec.ofNat 8 core, totalCore := 1, exception := .NoException, c_NextFetch := (fun _ => none), c_gpr := (fun _ reg => if reg = BitVec.ofNat 5 2 then BitVec.ofNat 64 b else 99), c_cycles := (fun _ => 77),       c_MCSR := (fun id => { base.c_MCSR id with mstatus := { (base.c_MCSR id).mstatus with MMPRV := false, MPRV := 0, MPRV1 := 3, VM := BitVec.ofNat 5 vm }, mcpuid := { (base.c_MCSR id).mcpuid with ArchBase := BitVec.ofNat 2 arch } }), c_SCSR := (fun id => { base.c_SCSR id with sasid := 63, sptbr := 0 }), c_tlb := (fun _ _ => none),       MEM8 := (fun x => if (x - BitVec.ofNat 64 v).toNat < 8 then BitVec.ofNat 8 (w / 2 ^ (8 * (x - BitVec.ofNat 64 v).toNat)) else 0) }

private def trapView : Option TransferControl → Nat × Option Nat
  | some (.Trap t) => ((if t.trap == .Load_Fault then 1 else if t.trap == .Illegal_Instr then 2 else 3),t.badaddr.map BitVec.toNat)
  | _ => (0,none)

private def tlbView (e : TLBEntry) :=
  (e.asid.toNat,e.global,e.vAddrMask.toNat,e.vMatchMask.toNat,e.vAddr.toNat,e.pAddr.toNat,e.age.toNat,e.pteAddr.toNat,e.pte.PTE_D,e.pte.PTE_PPNi.toNat,e.pte.PTE_R,e.pte.PTE_SW.toNat,e.pte.PTE_T.toNat,e.pte.PTE_V,e.pte.«sv_pte'rst».toNat)

private noncomputable def observation
    (f : (BitVec 5 × BitVec 5 × BitVec 12) → riscv_state → riscv_state)
    (s : riscv_state) (rd : BitVec 5) (offs : BitVec 12) (va : BitVec 64) := by
  classical
  exact
    let r := f (rd,2,offs) s
    ((GPR rd r).toNat,(r.c_gpr s.procID rd).toNat,(r.c_gpr (s.procID+1) rd).toNat,
      trapView (r.c_NextFetch s.procID),r.exception == .NoException,
      (rawReadData 0 r).toNat,(r.MEM8 va).toNat,(r.c_tlb s.procID 0).map tlbView,
      (r.c_tlb (s.procID+1) 0).map (fun e => e.pAddr.toNat),
      decide ({ r with MEM8 := s.MEM8, c_gpr := s.c_gpr, c_tlb := s.c_tlb, c_NextFetch := s.c_NextFetch, exception := s.exception } = s),
      r.totalCore,r.procID.toNat)

-- Original l3_integer_load_probe.out: lw_negative.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lw_positive.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (305419903,305419903,99,(0,none),true,1311768465173141119,127,none,none,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lw_rd_zero.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lw_unaligned.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,9223372036854775808,128,none,none,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lw_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lw_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'LW» (fixture base 3079 0 0 0 1 7 2 9)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (3111,3111,99,(0,none),true,3111,39,(some (63,false,1073741823,18446744072635809792,0,0,77,0,false,3,true,0,3,true,0)),none,true,1,7) := by
  simp only [observation, lwShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_negative.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (4132733056,4132733056,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_positive.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (305419903,305419903,99,(0,none),true,1311768465173141119,127,none,none,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_rd_zero.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_unaligned.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (4132733056,4132733056,99,(0,none),true,9223372036854775808,128,none,none,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (4132733056,4132733056,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lwu_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'LWU» (fixture base 3079 0 0 0 1 7 2 9)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (3111,3111,99,(0,none),true,3111,39,(some (63,false,1073741823,18446744072635809792,0,0,77,0,false,3,true,0,3,true,0)),none,true,1,7) := by
  simp only [observation, lwuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_negative.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18446744073709518976,18446744073709518976,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_positive.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (22143,22143,99,(0,none),true,1311768465173141119,127,none,none,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_rd_zero.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_unaligned.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (18446744073709518976,18446744073709518976,99,(0,none),true,9223372036854775808,128,none,none,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (18446744073709518976,18446744073709518976,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lh_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'LH» (fixture base 3079 0 0 0 1 7 2 9)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (3111,3111,99,(0,none),true,3111,39,(some (63,false,1073741823,18446744072635809792,0,0,77,0,false,3,true,0,3,true,0)),none,true,1,7) := by
  simp only [observation, lhShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_negative.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (32896,32896,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_positive.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (22143,22143,99,(0,none),true,1311768465173141119,127,none,none,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_rd_zero.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_unaligned.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (32896,32896,99,(0,none),true,9223372036854775808,128,none,none,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (32896,32896,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lhu_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'LHU» (fixture base 3079 0 0 0 1 7 2 9)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (3111,3111,99,(0,none),true,3111,39,(some (63,false,1073741823,18446744072635809792,0,0,77,0,false,3,true,0,3,true,0)),none,true,1,7) := by
  simp only [observation, lhuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_negative.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18446744073709551488,18446744073709551488,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_positive.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (127,127,99,(0,none),true,1311768465173141119,127,none,none,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_rd_zero.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_unaligned.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (18446744073709551488,18446744073709551488,99,(0,none),true,9223372036854775808,128,none,none,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (18446744073709551488,18446744073709551488,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lb_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'LB» (fixture base 3079 0 0 0 1 7 2 9)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (39,39,99,(0,none),true,3111,39,(some (63,false,1073741823,18446744072635809792,0,0,77,0,false,3,true,0,3,true,0)),none,true,1,7) := by
  simp only [observation, lbShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_negative.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (128,128,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_positive.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (127,127,99,(0,none),true,1311768465173141119,127,none,none,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_rd_zero.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_unaligned.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (128,128,99,(0,none),true,9223372036854775808,128,none,none,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (128,128,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: lbu_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'LBU» (fixture base 3079 0 0 0 1 7 2 9)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (39,39,99,(0,none),true,3111,39,(some (63,false,1073741823,18446744072635809792,0,0,77,0,false,3,true,0,3,true,0)),none,true,1,7) := by
  simp only [observation, lbuShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_negative.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_positive.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (1311768465173141119,1311768465173141119,99,(0,none),true,1311768465173141119,127,none,none,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_rd_zero.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_unaligned.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 8 7 4095 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (18364758546640568448,18364758546640568448,99,(0,none),true,9223372036854775808,128,none,none,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_offset_wrap.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 18446744073709551615 0 1 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_core_wrap.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 0 0 0 1 255 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,99,(0,none),true,18364758546640568448,128,none,none,true,1,255) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_fault_sv32.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 8 7 4095 1 7 2 8)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (99,99,99,(1,(some 7)),true,9223372036854775808,128,none,none,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_rv32_mode.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 0 0 0 1 7 0 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (99,99,99,(2,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_rv128_mode.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 18364758546640568448 0 0 0 1 7 3 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,99,(0,none),true,18364758546640568448,128,none,none,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_load_probe.out: ld_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'LD» (fixture base 3079 0 0 0 1 7 2 9)
      (BitVec.ofNat 5 1) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (3111,3111,99,(0,none),true,3111,39,(some (63,false,1073741823,18446744072635809792,0,0,77,0,false,3,true,0,3,true,0)),none,true,1,7) := by
  simp only [observation, ldShape]
  simp only [Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LW»,«dfn'LWU»,«dfn'LH»,«dfn'LHU»,«dfn'LB»,«dfn'LBU»,«dfn'LD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

end Flapjack.Test.L3IntegerLoadParity
