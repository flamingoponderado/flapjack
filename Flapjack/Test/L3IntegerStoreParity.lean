import Flapjack.RiscV.L3.Defs.IntegerStore
set_option maxRecDepth 200000
namespace Flapjack.Test.L3IntegerStoreParity
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
  { base with procID := BitVec.ofNat 8 core, totalCore := 1, exception := .NoException, c_NextFetch := (fun _ => none), c_gpr := (fun _ reg => if reg = BitVec.ofNat 5 2 then BitVec.ofNat 64 b else if reg = BitVec.ofNat 5 3 then 81985529216486895 else 99), c_cycles := (fun _ => 77),       c_MCSR := (fun id => { base.c_MCSR id with mstatus := { (base.c_MCSR id).mstatus with MMPRV := false, MPRV := 0, MPRV1 := 3, VM := BitVec.ofNat 5 vm }, mcpuid := { (base.c_MCSR id).mcpuid with ArchBase := BitVec.ofNat 2 arch } }), c_SCSR := (fun id => { base.c_SCSR id with sasid := 63, sptbr := 0 }), c_tlb := (fun _ _ => none), MEM8 := (fun x => if (x - BitVec.ofNat 64 v).toNat < 8 then BitVec.ofNat 8 (w / 2 ^ (8 * (x - BitVec.ofNat 64 v).toNat)) else 0) }

private def trapView : Option TransferControl → Nat × Option Nat
  | some (.Trap t) => ((if t.trap == .Load_Fault then 1 else if t.trap == .Illegal_Instr then 2 else if t.trap == .AMO_Misaligned then 3 else if t.trap == .Store_AMO_Fault then 4 else 5),t.badaddr.map BitVec.toNat)
  | _ => (0,none)

private def tlbView (e : TLBEntry) :=
  (e.asid.toNat,e.global,e.vAddrMask.toNat,e.vMatchMask.toNat,e.vAddr.toNat,e.pAddr.toNat,e.age.toNat,e.pteAddr.toNat,e.pte.PTE_D,e.pte.PTE_PPNi.toNat,e.pte.PTE_R,e.pte.PTE_SW.toNat,e.pte.PTE_T.toNat,e.pte.PTE_V,e.pte.«sv_pte'rst».toNat)

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
      (r.c_tlb s.procID 0).map tlbView,(r.c_tlb (s.procID+1) 0).map (fun e => e.pAddr.toNat),
      decide ({ r with MEM8 := s.MEM8, c_tlb := s.c_tlb, c_NextFetch := s.c_NextFetch, exception := s.exception } = s),
      r.totalCore,r.procID.toNat)

-- Original l3_integer_store_probe.out: sw_aligned.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_positive_memory.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 1311768465173141119 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,1311768467177459183,0,1311768467177459183,[239,205,171,137,120,86,52,18],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_rs2_zero.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758542507835392,0,18364758542507835392,[0,0,0,0,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_negative_offset_cross.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 8 7 4095 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17221764975064776704,71737338065693645,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_offset_wrap.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 18446744073709551615 0 1 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_address_wrap.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 18446744073709551615 18446744073709551615 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 18446744073709551615) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,71737338065693645,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_core_wrap.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 0 0 0 255 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,255) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_fault_sv32_unaligned.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 8 7 4095 0 7 2 8)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 7),true,9223372036854775808,71737338072814720,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_rv32_mode.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 0 0 0 7 0 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_rv128_mode.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 0 0 0 7 3 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_write_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 3079 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,2309737967,0,2309737967,[239,205,171,137,0,0,0,0],some (63,false,1073741823,18446744072635809792,0,0,77,0,true,3,true,0,3,true,0),none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_read_only_page_fault.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 3077 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 0),true,3077,0,3077,[5,12,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_invalid_pte_fault.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 0 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 0),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_positive_offset.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 0 4 4 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4) (BitVec.ofNat 64 4) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,9920249030594527232,4275878552,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sw_rs1_zero.
example (base : riscv_state) :
    observation «dfn'SW» (fixture base 18364758546640568448 99 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758544817573359,0,18364758544817573359,[239,205,171,137,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SW»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_aligned.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640588271,0,18364758546640588271,[239,205,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_positive_memory.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 1311768465173141119 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,1311768465173171695,0,1311768465173171695,[239,205,52,18,120,86,52,18],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_rs2_zero.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640535552,0,18364758546640535552,[0,0,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_negative_offset_cross.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 8 7 4095 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17221764975064776704,71737338072814797,18364758546640588271,[239,205,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_offset_wrap.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 18446744073709551615 0 1 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640588271,0,18364758546640588271,[239,205,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_address_wrap.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 18446744073709551615 18446744073709551615 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 18446744073709551615) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,71737338072814797,0,18364758546640588271,[239,205,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_core_wrap.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 0 0 0 0 255 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640588271,0,18364758546640588271,[239,205,84,246,152,186,220,254],none,none,true,1,255) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_fault_sv32_unaligned.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 8 7 4095 0 7 2 8)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 7),true,9223372036854775808,71737338072814720,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_rv32_mode.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 0 0 0 0 7 0 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640588271,0,18364758546640588271,[239,205,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_rv128_mode.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 0 0 0 0 7 3 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640588271,0,18364758546640588271,[239,205,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_write_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 3079 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,52719,0,52719,[239,205,0,0,0,0,0,0],some (63,false,1073741823,18446744072635809792,0,0,77,0,true,3,true,0,3,true,0),none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_read_only_page_fault.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 3077 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 0),true,3077,0,3077,[5,12,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_invalid_pte_fault.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 0 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 0),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_positive_offset.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 0 4 4 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4) (BitVec.ofNat 64 4) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17750038457754845184,4275878552,18364758546640588271,[239,205,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sh_rs1_zero.
example (base : riscv_state) :
    observation «dfn'SH» (fixture base 18364758546640568448 99 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640588271,0,18364758546640588271,[239,205,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SH»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_aligned.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568559,0,18364758546640568559,[239,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_positive_memory.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 1311768465173141119 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,1311768465173141231,0,1311768465173141231,[239,86,52,18,120,86,52,18],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_rs2_zero.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,18364758546640568320,0,18364758546640568320,[0,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_negative_offset_cross.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 8 7 4095 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17221764975064776704,71737338072814720,18364758546640568559,[239,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_offset_wrap.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 18446744073709551615 0 1 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568559,0,18364758546640568559,[239,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_address_wrap.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 18446744073709551615 18446744073709551615 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 18446744073709551615) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,71737338072814720,0,18364758546640568559,[239,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_core_wrap.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 0 0 0 0 255 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568559,0,18364758546640568559,[239,128,84,246,152,186,220,254],none,none,true,1,255) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_fault_sv32_unaligned.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 8 7 4095 0 7 2 8)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 7),true,9223372036854775808,71737338072814720,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_rv32_mode.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 0 0 0 0 7 0 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568559,0,18364758546640568559,[239,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_rv128_mode.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 0 0 0 0 7 3 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568559,0,18364758546640568559,[239,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_write_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 3079 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,3311,0,3311,[239,12,0,0,0,0,0,0],some (63,false,1073741823,18446744072635809792,0,0,77,0,true,3,true,0,3,true,0),none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_read_only_page_fault.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 3077 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 0),true,3077,0,3077,[5,12,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_invalid_pte_fault.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 0 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 0),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_positive_offset.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 0 4 4 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4) (BitVec.ofNat 64 4) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17749953795359506432,4275878552,18364758546640568559,[239,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sb_rs1_zero.
example (base : riscv_state) :
    observation «dfn'SB» (fixture base 18364758546640568448 99 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,18364758546640568559,0,18364758546640568559,[239,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SB»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_aligned.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_positive_memory.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 1311768465173141119 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_rs2_zero.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 0 0 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 0) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (0,99,99,(0,none),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_negative_offset_cross.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 8 7 4095 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,17221764975064776704,320255973501901,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_offset_wrap.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 18446744073709551615 0 1 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 1) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_address_wrap.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 18446744073709551615 18446744073709551615 0 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 18446744073709551615) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,320255973501901,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_core_wrap.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 0 0 0 0 255 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,255) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_fault_sv32_unaligned.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 8 7 4095 0 7 2 8)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4095) (BitVec.ofNat 64 7) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 7),true,9223372036854775808,71737338072814720,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_rv32_mode.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 0 0 0 0 7 0 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(2,none),true,18364758546640568448,0,18364758546640568448,[128,128,84,246,152,186,220,254],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_rv128_mode.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 0 0 0 0 7 3 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_write_walk_returned_state.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 3079 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],some (63,false,1073741823,18446744072635809792,0,0,77,0,true,3,true,0,3,true,0),none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_read_only_page_fault.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 3077 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 0),true,3077,0,3077,[5,12,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_invalid_pte_fault.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 0 0 0 0 0 7 2 9)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(4,some 0),true,0,0,0,[0,0,0,0,0,0,0,0],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_positive_offset.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 0 4 4 0 7 2 0)
      (BitVec.ofNat 5 2) (BitVec.ofNat 5 3) (BitVec.ofNat 12 4) (BitVec.ofNat 64 4) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,9920249030594527232,19088743,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

-- Original l3_integer_store_probe.out: sd_rs1_zero.
example (base : riscv_state) :
    observation «dfn'SD» (fixture base 18364758546640568448 99 0 0 0 7 2 0)
      (BitVec.ofNat 5 0) (BitVec.ofNat 5 3) (BitVec.ofNat 12 0) (BitVec.ofNat 64 0) =
      (81985529216486895,81985529216486895,81985529216486895,(0,none),true,81985529216486895,0,81985529216486895,[239,205,171,137,103,69,35,1],none,none,true,1,7) := by
  simp only [observation, Prod.mk.injEq]
  repeat' apply And.intro
  all_goals simp [«dfn'SD»,fixture,trapView,tlbView,singletonWord,writeFullWord,lookupEmpty,insertEmpty,
    GPR,gpr,signalAddressException,signalException,setTrap,«write'NextFetch»,
    in32BitMode,curArch,architecture,translateAddr,MCSR,vmType,privilege,translate64,curASID,ASID_SIZE,
    SCSR,TLB,«write'TLB»,mkTLBEntry,lookupTLB,TLBEntries,Flapjack.holFor,walk64,rawReadData,rawWriteData,MEM,«write'MEM»,
    «rec'SV_Vaddr»,«rec'SV_PTE»,«reg'SV_PTE»,checkMemPermission,isGlobal,LEVEL_BITS,PAGESIZE_BITS,holWordExtract,
    holUpdate,List.range_succ,List.map] <;> decide

end Flapjack.Test.L3IntegerStoreParity
