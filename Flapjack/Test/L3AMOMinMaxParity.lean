import Flapjack.RiscV.L3.Defs.AMOMinMax
set_option maxRecDepth 200000
namespace Flapjack.Test.L3AMOMinMaxParity
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


private def fixture (base : riscv_state) (w b v o rd core arch vm value : Nat) : riscv_state :=
  { base with procID := BitVec.ofNat 8 core, totalCore := 1, exception := .NoException, c_NextFetch := (fun _ => none), c_gpr := (fun _ reg => if reg = BitVec.ofNat 5 2 then BitVec.ofNat 64 b else if reg = BitVec.ofNat 5 3 then BitVec.ofNat 64 value else 99), c_cycles := (fun _ => 77),       c_MCSR := (fun id => { base.c_MCSR id with mstatus := { (base.c_MCSR id).mstatus with MMPRV := false, MPRV := 0, MPRV1 := 3, VM := BitVec.ofNat 5 vm }, mcpuid := { (base.c_MCSR id).mcpuid with ArchBase := BitVec.ofNat 2 arch } }), c_SCSR := (fun id => { base.c_SCSR id with sasid := 63, sptbr := 0 }), c_tlb := (fun _ _ => none), MEM8 := (fun x => if (x - BitVec.ofNat 64 v).toNat < 8 then BitVec.ofNat 8 (w / 2 ^ (8 * (x - BitVec.ofNat 64 v).toNat)) else 0) }

private def trapView : Option TransferControl → Nat × Option Nat
  | some (.Trap t) => ((if t.trap == .Load_Fault then 1 else if t.trap == .Illegal_Instr then 2 else if t.trap == .AMO_Misaligned then 3 else if t.trap == .Store_AMO_Fault then 4 else 5),t.badaddr.map BitVec.toNat)
  | _ => (0,none)

private def tlbView (e : TLBEntry) :=
  (e.asid.toNat,e.global,e.vAddrMask.toNat,e.vMatchMask.toNat,e.vAddr.toNat,e.pAddr.toNat,e.age.toNat,e.pteAddr.toNat,e.pte.PTE_D,e.pte.PTE_PPNi.toNat,e.pte.PTE_R,e.pte.PTE_SW.toNat,e.pte.PTE_T.toNat,e.pte.PTE_V,e.pte.«sv_pte'rst».toNat)

private noncomputable def observation
    (f : (BitVec 1 × BitVec 1 × BitVec 5 × BitVec 5 × BitVec 5) → riscv_state → riscv_state)
    (s : riscv_state) (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5) (va : BitVec 64) := by
  classical
  exact
    let r := f (aq,rl,rd,rs1,rs2) s
    ((GPR rs2 r).toNat,(r.c_gpr s.procID rs2).toNat,(r.c_gpr (s.procID+1) rs2).toNat,
      trapView (r.c_NextFetch s.procID),r.exception == .NoException,
      (rawReadData 0 r).toNat,(rawReadData 8 r).toNat,(rawReadData va r).toNat,
      (List.range 8).map (fun i => (r.MEM8 (va+BitVec.ofNat 64 i)).toNat),
      (r.c_tlb s.procID 0).map tlbView,(r.c_tlb (s.procID+1) 0).map (fun e => e.pAddr.toNat),
      decide ({ r with c_gpr := s.c_gpr, MEM8 := s.MEM8, c_tlb := s.c_tlb, c_NextFetch := s.c_NextFetch, exception := s.exception } = s),
      r.totalCore,r.procID.toNat)

-- Original amomin_w_aligned_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_aligned_rd0; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 0 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_aligned_rd2; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 2 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_positive_memory_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 1311768465173141119 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (305419903,305419903,81985529216486895,(0,none),true,1311768465173141119,0,1311768465173141119,[127,86,52,18,120,86,52,18],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_rs2_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 0 (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_address_wrap_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 18446744073709551615 18446744073709551615 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 18446744073709551615) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 18446744073709551615)),true,71737338072814720,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_core_wrap_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 0 0 0 0 255 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,255) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_rv32_mode_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 0 0 0 0 7 0 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_rv128_mode_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 0 0 0 0 7 3 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_write_walk_returned_state_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 3079 0 0 0 0 7 2 9 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (3175,3175,81985529216486895,(0,none),true,3175,0,3175,[103,12,0,0,0,0,0,0],(some (63,false,1073741823,18446744072635809792,0,0,77,0,true,3,true,0,3,true,0)),none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_read_only_page_fault_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 3077 0 0 0 0 7 2 9 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,(some 0)),true,3077,0,3077,[5,12,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_invalid_pte_fault_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 0 0 0 0 0 7 2 9 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,(some 0)),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_rs1_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 99 0 0 0 7 2 0 81985529216486895)
      0 0 3 0 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_aligned_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_aligned_rd0; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 0 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_aligned_rd2; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 2 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_positive_memory_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 1311768465173141119 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1311768465173141119,1311768465173141119,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_rs2_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 0 (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_address_wrap_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 18446744073709551615 18446744073709551615 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 18446744073709551615) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 18446744073709551615)),true,71737338072814720,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_core_wrap_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 0 0 0 0 255 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,255) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_rv32_mode_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 0 0 0 0 7 0 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_rv128_mode_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 0 0 0 0 7 3 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_write_walk_returned_state_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 3079 0 0 0 0 7 2 9 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (3175,3175,81985529216486895,(0,none),true,3175,0,3175,[103,12,0,0,0,0,0,0],(some (63,false,1073741823,18446744072635809792,0,0,77,0,true,3,true,0,3,true,0)),none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_read_only_page_fault_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 3077 0 0 0 0 7 2 9 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,(some 0)),true,3077,0,3077,[5,12,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_invalid_pte_fault_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 0 0 0 0 0 7 2 9 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,(some 0)),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_rs1_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 99 0 0 0 7 2 0 81985529216486895)
      0 0 3 0 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_overflow_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18446744073709551615 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073709551615,18446744073709551615,18446744073709551615,(0,none),true,18446744073709551615,0,18446744073709551615,[255,255,255,255,255,255,255,255],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_order_0_1_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 1 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_order_1_0_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      1 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_order_1_1_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      1 1 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_misaligned_1_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 1 1 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 1) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 1)),true,15905193217759412224,254,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_misaligned_2_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 2 2 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 2) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 2)),true,13445767530308173824,65244,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_misaligned_3_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 18364758546640568448 3 3 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 3) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 3)),true,11022090048915898368,16702650,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_overflow_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18446744073709551615 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073709551615,18446744073709551615,18446744073709551615,(0,none),true,18446744073709551615,0,18446744073709551615,[255,255,255,255,255,255,255,255],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_order_0_1_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 1 3 2 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_order_1_0_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      1 0 3 2 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_order_1_1_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      1 1 3 2 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_misaligned_1_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 1 1 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 1) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 1)),true,15905193217759412224,254,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_misaligned_2_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 2 2 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 2) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 2)),true,13445767530308173824,65244,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_misaligned_3_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 3 3 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 3) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 3)),true,11022090048915898368,16702650,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_misaligned_4_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 4 4 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 4) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 4)),true,17749953318618136576,4275878552,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_misaligned_5_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 5 5 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 5) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 5)),true,6089007433693265920,1094624909558,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_misaligned_6_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 6 6 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 6) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 6)),true,9259400833873739776,280223976846932,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_misaligned_7_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 18364758546640568448 7 7 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(3,(some 7)),true,9223372036854775808,71737338072814720,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_both_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 0 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (0,0,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_equal_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 17 0 0 0 0 7 2 0 17)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (17,17,17,(0,none),true,17,0,17,[17,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_old_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 2147483648 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744071562067968,18446744071562067968,0,(0,none),true,2147483648,0,2147483648,[0,0,0,128,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_source_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 1 0 0 0 0 7 2 0 9223372036854775808)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,9223372036854775808,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_old_signed_max_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 2147483647 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (2147483647,2147483647,18446744073709551615,(0,none),true,4294967295,0,4294967295,[255,255,255,255,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_w_source_upper32_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_W» (fixture base 1 0 0 0 0 7 2 0 4294967296)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,4294967296,(0,none),true,1,0,1,[1,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_both_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 0 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (0,0,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_equal_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 17 0 0 0 0 7 2 0 17)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (17,17,17,(0,none),true,17,0,17,[17,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_old_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 9223372036854775808 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (9223372036854775808,9223372036854775808,0,(0,none),true,9223372036854775808,0,9223372036854775808,[0,0,0,0,0,0,0,128],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_source_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 1 0 0 0 0 7 2 0 9223372036854775808)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,9223372036854775808,(0,none),true,9223372036854775808,0,9223372036854775808,[0,0,0,0,0,0,0,128],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_old_signed_max_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 9223372036854775807 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (9223372036854775807,9223372036854775807,18446744073709551615,(0,none),true,18446744073709551615,0,18446744073709551615,[255,255,255,255,255,255,255,255],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomin_d_source_upper32_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMIN_D» (fixture base 1 0 0 0 0 7 2 0 4294967296)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,4294967296,(0,none),true,1,0,1,[1,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMIN_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_aligned_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_aligned_rd0; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 0 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_aligned_rd2; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 2 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_positive_memory_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 1311768465173141119 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (305419903,305419903,81985529216486895,(0,none),true,1311768467177459183,0,1311768467177459183,[239,205,171,137,120,86,52,18],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_rs2_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 0 (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758542507835392,0,18364758542507835392,[0,0,0,0,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_rs1_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 18364758546640568448 99 0 0 0 7 2 0 81985529216486895)
      0 0 3 0 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_aligned_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_aligned_rd0; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 0 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_aligned_rd2; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 2 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_positive_memory_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 1311768465173141119 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1311768465173141119,1311768465173141119,81985529216486895,(0,none),true,1311768465173141119,0,1311768465173141119,[127,86,52,18,120,86,52,18],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_rs2_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 0 (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_rs1_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 18364758546640568448 99 0 0 0 7 2 0 81985529216486895)
      0 0 3 0 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_overflow_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 18446744073709551615 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073709551615,18446744073709551615,18446744073709551615,(0,none),true,18446744073709551615,0,18446744073709551615,[255,255,255,255,255,255,255,255],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_overflow_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 18446744073709551615 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073709551615,18446744073709551615,18446744073709551615,(0,none),true,18446744073709551615,0,18446744073709551615,[255,255,255,255,255,255,255,255],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_both_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 0 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (0,0,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_equal_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 17 0 0 0 0 7 2 0 17)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (17,17,17,(0,none),true,17,0,17,[17,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_old_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 2147483648 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744071562067968,18446744071562067968,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_source_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 1 0 0 0 0 7 2 0 9223372036854775808)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,9223372036854775808,(0,none),true,1,0,1,[1,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_old_signed_max_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 2147483647 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (2147483647,2147483647,18446744073709551615,(0,none),true,2147483647,0,2147483647,[255,255,255,127,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_w_source_upper32_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_W» (fixture base 1 0 0 0 0 7 2 0 4294967296)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,4294967296,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_both_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 0 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (0,0,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_equal_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 17 0 0 0 0 7 2 0 17)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (17,17,17,(0,none),true,17,0,17,[17,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_old_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 9223372036854775808 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (9223372036854775808,9223372036854775808,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_source_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 1 0 0 0 0 7 2 0 9223372036854775808)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,9223372036854775808,(0,none),true,1,0,1,[1,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_old_signed_max_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 9223372036854775807 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (9223372036854775807,9223372036854775807,18446744073709551615,(0,none),true,9223372036854775807,0,9223372036854775807,[255,255,255,255,255,255,255,127],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomax_d_source_upper32_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAX_D» (fixture base 1 0 0 0 0 7 2 0 4294967296)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,4294967296,(0,none),true,4294967296,0,4294967296,[0,0,0,0,1,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAX_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_aligned_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_aligned_rd0; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 0 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_aligned_rd2; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 2 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_positive_memory_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 1311768465173141119 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (305419903,305419903,81985529216486895,(0,none),true,1311768465173141119,0,1311768465173141119,[127,86,52,18,120,86,52,18],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_rs2_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 0 (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758542507835392,0,18364758542507835392,[0,0,0,0,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_rs1_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 18364758546640568448 99 0 0 0 7 2 0 81985529216486895)
      0 0 3 0 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_aligned_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_aligned_rd0; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 0 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_aligned_rd2; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 2 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_positive_memory_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 1311768465173141119 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1311768465173141119,1311768465173141119,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_rs2_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 0 (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_rs1_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 18364758546640568448 99 0 0 0 7 2 0 81985529216486895)
      0 0 3 0 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_overflow_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 18446744073709551615 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073709551615,18446744073709551615,18446744073709551615,(0,none),true,18446744073709551615,0,18446744073709551615,[255,255,255,255,255,255,255,255],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_overflow_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 18446744073709551615 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073709551615,18446744073709551615,18446744073709551615,(0,none),true,18446744073709551615,0,18446744073709551615,[255,255,255,255,255,255,255,255],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_both_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 0 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (0,0,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_equal_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 17 0 0 0 0 7 2 0 17)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (17,17,17,(0,none),true,17,0,17,[17,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_old_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 2147483648 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744071562067968,18446744071562067968,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_source_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 1 0 0 0 0 7 2 0 9223372036854775808)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,9223372036854775808,(0,none),true,1,0,1,[1,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_old_signed_max_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 2147483647 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (2147483647,2147483647,18446744073709551615,(0,none),true,2147483647,0,2147483647,[255,255,255,127,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_w_source_upper32_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_W» (fixture base 1 0 0 0 0 7 2 0 4294967296)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,4294967296,(0,none),true,1,0,1,[1,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_both_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 0 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (0,0,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_equal_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 17 0 0 0 0 7 2 0 17)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (17,17,17,(0,none),true,17,0,17,[17,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_old_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 9223372036854775808 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (9223372036854775808,9223372036854775808,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_source_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 1 0 0 0 0 7 2 0 9223372036854775808)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,9223372036854775808,(0,none),true,1,0,1,[1,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_old_signed_max_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 9223372036854775807 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (9223372036854775807,9223372036854775807,18446744073709551615,(0,none),true,9223372036854775807,0,9223372036854775807,[255,255,255,255,255,255,255,127],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amominu_d_source_upper32_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMINU_D» (fixture base 1 0 0 0 0 7 2 0 4294967296)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,4294967296,(0,none),true,1,0,1,[1,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMINU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_aligned_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_aligned_rd0; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 0 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_aligned_rd2; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 2 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_positive_memory_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 1311768465173141119 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (305419903,305419903,81985529216486895,(0,none),true,1311768467177459183,0,1311768467177459183,[239,205,171,137,120,86,52,18],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_rs2_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 0 (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_rs1_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 18364758546640568448 99 0 0 0 7 2 0 81985529216486895)
      0 0 3 0 3 (BitVec.ofNat 64 0) =
      (18446744073547317376,18446744073547317376,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_aligned_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_aligned_rd0; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 0 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_aligned_rd2; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 2 2 3 (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_positive_memory_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 1311768465173141119 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1311768465173141119,1311768465173141119,81985529216486895,(0,none),true,1311768465173141119,0,1311768465173141119,[127,86,52,18,120,86,52,18],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_rs2_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 18364758546640568448 0 0 0 0 7 2 0 81985529216486895)
      0 0 3 2 0 (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_rs1_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 18364758546640568448 99 0 0 0 7 2 0 81985529216486895)
      0 0 3 0 3 (BitVec.ofNat 64 0) =
      (18364758546640568448,18364758546640568448,81985529216486895,(0,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_overflow_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 18446744073709551615 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073709551615,18446744073709551615,18446744073709551615,(0,none),true,18446744073709551615,0,18446744073709551615,[255,255,255,255,255,255,255,255],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_overflow_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 18446744073709551615 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744073709551615,18446744073709551615,18446744073709551615,(0,none),true,18446744073709551615,0,18446744073709551615,[255,255,255,255,255,255,255,255],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_both_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 0 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (0,0,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_equal_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 17 0 0 0 0 7 2 0 17)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (17,17,17,(0,none),true,17,0,17,[17,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_old_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 2147483648 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (18446744071562067968,18446744071562067968,0,(0,none),true,2147483648,0,2147483648,[0,0,0,128,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_source_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 1 0 0 0 0 7 2 0 9223372036854775808)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,9223372036854775808,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_old_signed_max_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 2147483647 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (2147483647,2147483647,18446744073709551615,(0,none),true,4294967295,0,4294967295,[255,255,255,255,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_w_source_upper32_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_W» (fixture base 1 0 0 0 0 7 2 0 4294967296)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,4294967296,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_W»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_both_zero_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 0 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (0,0,0,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_equal_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 17 0 0 0 0 7 2 0 17)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (17,17,17,(0,none),true,17,0,17,[17,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_old_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 9223372036854775808 0 0 0 0 7 2 0 0)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (9223372036854775808,9223372036854775808,0,(0,none),true,9223372036854775808,0,9223372036854775808,[0,0,0,0,0,0,0,128],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_source_signed_min_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 1 0 0 0 0 7 2 0 9223372036854775808)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,9223372036854775808,(0,none),true,9223372036854775808,0,9223372036854775808,[0,0,0,0,0,0,0,128],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_old_signed_max_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 9223372036854775807 0 0 0 0 7 2 0 18446744073709551615)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (9223372036854775807,9223372036854775807,18446744073709551615,(0,none),true,18446744073709551615,0,18446744073709551615,[255,255,255,255,255,255,255,255],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


-- Original amomaxu_d_source_upper32_rd3; independent byte/register expectations.
example (base : riscv_state) :
    observation «dfn'AMOMAXU_D» (fixture base 1 0 0 0 0 7 2 0 4294967296)
      0 0 3 2 3 (BitVec.ofNat 64 0) =
      (1,1,4294967296,(0,none),true,4294967296,0,4294967296,[0,0,0,0,1,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'AMOMAXU_D»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,«write'GPR»,«write'gpr»,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide


end Flapjack.Test.L3AMOMinMaxParity
