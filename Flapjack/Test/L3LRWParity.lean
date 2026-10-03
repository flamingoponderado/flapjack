import Flapjack.RiscV.L3.Defs.LRSC
set_option maxRecDepth 200000
namespace Flapjack.Test.L3LRWParity
open Flapjack.RiscV.L3
/-! Flapjack-only original-oracle regressions, not whole atomic/runtime correctness.
Arbitrary unrelated native fields are retained; every observed frame resets only
fields the exact instruction may change. No standalone HOL theorem is claimed. -/
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
  { base with procID := BitVec.ofNat 8 core, totalCore := 1, exception := .NoException, c_NextFetch := (fun _ => none), c_gpr := (fun _ reg => if reg = BitVec.ofNat 5 2 then BitVec.ofNat 64 b else 99), c_cycles := (fun _ => 77),       c_MCSR := (fun id => { base.c_MCSR id with mstatus := { (base.c_MCSR id).mstatus with MMPRV := false, MPRV := 0, MPRV1 := 3, VM := BitVec.ofNat 5 vm }, mcpuid := { (base.c_MCSR id).mcpuid with ArchBase := BitVec.ofNat 2 arch } }), c_SCSR := (fun id => { base.c_SCSR id with sasid := 63, sptbr := 0 }), c_tlb := (fun _ _ => none), c_ReserveLoad := (fun _ => some 21),       MEM8 := (fun x => if (x - BitVec.ofNat 64 v).toNat < 8 then BitVec.ofNat 8 (w / 2 ^ (8 * (x - BitVec.ofNat 64 v).toNat)) else 0) }

private def trapView : Option TransferControl → Nat × Option Nat
  | some (.Trap t) => ((if t.trap == .Load_Fault then 1 else if t.trap == .Illegal_Instr then 2 else if t.trap == .AMO_Misaligned then 3 else 4),t.badaddr.map BitVec.toNat)
  | _ => (0,none)

private def tlbView (e : TLBEntry) :=
  (e.asid.toNat,e.global,e.vAddrMask.toNat,e.vMatchMask.toNat,e.vAddr.toNat,e.pAddr.toNat,e.age.toNat,e.pteAddr.toNat,e.pte.PTE_D,e.pte.PTE_PPNi.toNat,e.pte.PTE_R,e.pte.PTE_SW.toNat,e.pte.PTE_T.toNat,e.pte.PTE_V,e.pte.«sv_pte'rst».toNat)

private noncomputable def observation (s : riscv_state) (rd : BitVec 5)
    (aq rl : BitVec 1) (va : BitVec 64) := by
  classical
  exact
    let r := «dfn'LR_W» (aq,rl,rd,2) s
    ((GPR rd r).toNat,(r.c_gpr s.procID rd).toNat,(r.c_gpr (s.procID+1) rd).toNat,
      trapView (r.c_NextFetch s.procID),r.exception == .NoException,
      (rawReadData 0 r).toNat,(r.MEM8 va).toNat,(r.c_tlb s.procID 0).map tlbView,
      (r.c_tlb (s.procID+1) 0).map (fun e => e.pAddr.toNat),
      decide ({ r with MEM8 := s.MEM8, c_gpr := s.c_gpr, c_tlb := s.c_tlb, c_NextFetch := s.c_NextFetch, exception := s.exception, c_ReserveLoad := s.c_ReserveLoad } = s),
      r.totalCore,r.procID.toNat,(ReserveLoad r).map BitVec.toNat,
      (r.c_ReserveLoad (s.procID+1)).map BitVec.toNat)

-- Original l3_lrw_probe.out: lrw_negative.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,none,none,true,1,7,some 0,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_positive.
example (base : riscv_state) :
    observation (fixture base 1311768465173141119 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 0) =
      (305419903,305419903,99,(0,none),true,1311768465173141119,127,none,none,true,1,7,some 0,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_rd_zero.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,128,none,none,true,1,7,some 0,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_core_wrap.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 0 0 0 1 255 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,none,none,true,1,255,some 0,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_fault_sv32.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 8 8 0 1 7 2 8)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 8) =
      (99,99,99,(1,some 8),true,0,128,none,none,true,1,7,some 21,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_rv32_mode.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 0 0 0 1 7 0 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,none,none,true,1,7,some 0,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_rv128_mode.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 0 0 0 1 7 3 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,none,none,true,1,7,some 0,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_walk_returned_state.
example (base : riscv_state) :
    observation (fixture base 3079 0 0 0 1 7 2 9)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 0) =
      (3111,3111,99,(0,none),true,3111,39,some (63,false,1073741823,18446744072635809792,0,0,77,0,false,3,true,0,3,true,0),none,true,1,7,some 0,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_misaligned_1.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 1 1 0 1 7 2 8)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 1) =
      (99,99,99,(3,some 1),true,15905193217759412224,128,none,none,true,1,7,some 21,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_misaligned_2.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 2 2 0 1 7 2 8)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 2) =
      (99,99,99,(3,some 2),true,13445767530308173824,128,none,none,true,1,7,some 21,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_misaligned_3.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 3 3 0 1 7 2 8)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 0) (BitVec.ofNat 64 3) =
      (99,99,99,(3,some 3),true,11022090048915898368,128,none,none,true,1,7,some 21,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_order_0_1.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 0) (BitVec.ofNat 1 1) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,none,none,true,1,7,some 0,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_order_1_0.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 1) (BitVec.ofNat 1 0) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,none,none,true,1,7,some 0,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_lrw_probe.out: lrw_order_1_1.
example (base : riscv_state) :
    observation (fixture base 18364758546640568448 0 0 0 1 7 2 0)
      (BitVec.ofNat 5 1) (BitVec.ofNat 1 1) (BitVec.ofNat 1 1) (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,99,(0,none),true,18364758546640568448,128,none,none,true,1,7,some 0,some 21) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'LR_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    ReserveLoad,«write'ReserveLoad»,GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

end Flapjack.Test.L3LRWParity
