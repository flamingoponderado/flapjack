import Flapjack.RiscV.L3.Defs.Fetch
set_option maxRecDepth 200000
namespace Flapjack.Test
open Flapjack.RiscV.L3

-- Flapjack regression expectation: all nine original Delta fields are reset.
-- This test helper has no standalone HOL original.
private def fetchedDelta (pc : BitVec 64) (inst : rawInstType) : StateDelta :=
  { exc_taken := false, fetch_exc := false, pc := pc, rinstr := inst,
    addr := none, data1 := none, data2 := none, fp_data := none, st_width := none }

-- Flapjack-specific normalization facts for the regression, with no
-- independently named HOL originals. They preserve complete native states.
private theorem deltaAfterWrite (v : StateDelta) (s : riscv_state) :
    Delta («write'Delta» v s) = v := by
  simp [Delta, «write'Delta», holUpdate]

private theorem overwriteDelta (v w : StateDelta) (s : riscv_state) :
    «write'Delta» v («write'Delta» w s) = «write'Delta» v s := by
  cases s
  simp [«write'Delta»]
  funext k
  simp only [holUpdate]
  split <;> rfl

-- Flapjack regression normal form, with no standalone HOL original.
private noncomputable def fetchExpected (s : riscv_state) : FetchResult × riscv_state :=
  if (PC s).getLsbD 0 then
    (FetchResult.F_Error (instruction.Internal (Internal.FETCH_MISALIGNED (PC s))), s)
  else
    let (addr, t) := translateAddr (PC s, fetchType.Instruction, accessType.Read) s
    match addr with
    | none => (FetchResult.F_Error (instruction.Internal (Internal.FETCH_FAULT (PC s))), t)
    | some a =>
      let (inst, u) := rawReadInst a t
      (FetchResult.F_Result inst,
        { u with c_update := holUpdate u.procID (fetchedDelta (PC s) inst) u.c_update })

-- Unconditional whole-state equation: no alignment/success/core-bound premise.
private theorem modelFetchShape (s : riscv_state) : Fetch () s = fetchExpected s := by
  simp only [Fetch, deltaAfterWrite, overwriteDelta]
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

-- Numeric statements retain arbitrary unrelated native state fields.
-- The full-state equation above independently covers every untouched field.
private def resultView : FetchResult → Nat × Nat × Nat
  | .F_Result (.Half w) => (0, 16, w.toNat)
  | .F_Result (.Word w) => (0, 32, w.toNat)
  | .F_Error (.Internal (.FETCH_MISALIGNED v)) => (1, 0, v.toNat)
  | .F_Error (.Internal (.FETCH_FAULT v)) => (2, 0, v.toNat)
  | _ => (3, 0, 0)
private def deltaView (d : StateDelta) :=
  (d.exc_taken, d.fetch_exc, d.pc.toNat,
   (match d.rinstr with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
   d.addr.map BitVec.toNat, d.data1.map BitVec.toNat, d.data2.map BitVec.toNat,
   d.fp_data.map BitVec.toNat, d.st_width.map BitVec.toNat)
private def tlbView (e : TLBEntry) :=
  (e.asid.toNat, e.global, e.vAddrMask.toNat, e.vMatchMask.toNat,
   e.vAddr.toNat, e.pAddr.toNat, e.age.toNat, e.pteAddr.toNat,
   («reg'SV_PTE» e.pte).toNat)

-- Original HOL oracle odd_unknown_vm; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 1
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 1, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 31 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((1, 0, 1), 99, 99, [(true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 370240783104, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle odd_wrap; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 18446744073709551615
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 18446744073709551615, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 9 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((1, 0, 18446744073709551615), 99, 99, [(true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 5649426, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle none_vm_1; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 2
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 2, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 1 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((2, 0, 2), 99, 99, [(true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 94781640474624, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle none_vm_2; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 2
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 2, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 2 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((2, 0, 2), 99, 99, [(true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 94781640474624, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle none_vm_8; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 2
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 2, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 8 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((2, 0, 2), 99, 99, [(true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 94781640474624, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle none_vm_11; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 2
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 2, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 11 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((2, 0, 2), 99, 99, [(true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 94781640474624, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle none_vm_12; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 2
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 2, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 12 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((2, 0, 2), 99, 99, [(true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 94781640474624, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle bare_0_0; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 0
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 0, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 0 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 0 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((0, 16, 4608), 2, 99, [(false, false, 0, (16, 4608), none, none, none, none, none), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 1446253056, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 0, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle bare_0_3; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 0
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 0, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 0 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((0, 32, 1446253059), 4, 99, [(false, false, 0, (32, 1446253059), none, none, none, none, none), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 1446253059, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle bare_2_3; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 2
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 2, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 0 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((0, 32, 1446253059), 4, 99, [(false, false, 2, (32, 1446253059), none, none, none, none, none), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 94781640474624, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle bare_18446744073709551614_0; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 18446744073709551614
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 18446744073709551614, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 0 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 0 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((0, 16, 4608), 2, 99, [(false, false, 18446744073709551614, (16, 4608), none, none, none, none, none), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 22068, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 0, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle bare_18446744073709551614_3; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 18446744073709551614
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 18446744073709551614, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 0 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((0, 32, 1446253059), 4, 99, [(false, false, 18446744073709551614, (32, 1446253059), none, none, none, none, none), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 22068, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle hit_sv39; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 9848
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 1656, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 9 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun j => if j == (4 : BitVec 4) then some e else none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((0, 32, 1446253059), 4, 99, [(false, false, 1656, (32, 1446253059), none, none, none, none, none), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 0, [none, none, none, none, some (63, false, 4095, 18446744073709547520, 0, 8192, 88, 0, 3079), none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle hit_sv48_half; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 9848
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 1656, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 10 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun j => if j == (4 : BitVec 4) then some e else none),
       MEM8 := fun x => if x == a then 0 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((0, 16, 4608), 2, 99, [(false, false, 1656, (16, 4608), none, none, none, none, none), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 0, [none, none, none, none, some (63, false, 4095, 18446744073709547520, 0, 8192, 88, 0, 3079), none, none, none, none, none, none, none, none, none, none, none], true, 0, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle hit_denied; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 9848
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 1656, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 1, MPRV1 := 3, VM := 9 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun j => if j == (4 : BitVec 4) then some e else none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((2, 0, 1656), 99, 99, [(true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 0, [none, none, none, none, some (63, false, 4095, 18446744073709547520, 0, 8192, 88, 0, 3079), none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle walk_sv39; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 13944
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 1656, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 9 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 7 else if x == 1 then 12 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((0, 16, 0), 2, 99, [(false, false, 1656, (16, 0), none, none, none, none, none), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 3111, [some (63, false, 1073741823, 18446744072635809792, 0, 0, 77, 0, 3111), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle walk_sv48; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 13944
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 1656, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 10 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 0 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 7 else if x == 1 then 12 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((0, 16, 0), 2, 99, [(false, false, 1656, (16, 0), none, none, none, none, none), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 3111, [some (63, false, 549755813887, 18446743523953737728, 0, 0, 77, 0, 3111), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 0, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

-- Original HOL oracle walk_invalid; all nine Delta and all sixteen TLB slots.
example (base : riscv_state) :
    (let a : BitVec 64 := 13944
     let e : TLBEntry := { (default : TLBEntry) with
       asid := 63, global := false,
       vAddrMask := 4095, vMatchMask := 18446744073709547520, vAddr := 0,
       pAddr := 8192, age := 88, pteAddr := 0, pte := «rec'SV_PTE» 3079 }
     let s : riscv_state := { base with
       procID := 7, totalCore := 1, exception := exception.NoException,
       c_PC := fun _ => 1656, c_Skip := fun _ => 99, c_cycles := fun _ => 77,
       c_update := fun _ => {
         addr := some 21, data1 := some 22, data2 := some 23,
         exc_taken := true, fetch_exc := true, fp_data := some 24, pc := 11,
         rinstr := rawInstType.Half 48879, st_width := some 8 },
       c_MCSR := fun _ => { (default : MachineCSR) with
         mstatus := { (default : mstatus) with MMPRV := true, MPRV := 0, MPRV1 := 3, VM := 9 } },
       c_SCSR := fun _ => { (default : SupervisorCSR) with sasid := 63, sptbr := 0 },
       c_tlb := fun _ => (fun _ => none),
       MEM8 := fun x => if x == a then 3 else if x == a+1 then 18
         else if x == a+2 then 52 else if x == a+3 then 86
         else if x == 0 then 0 else if x == 1 then 0 else if x == 2 then 0 else if x == 3 then 0 else if x == 4 then 0 else if x == 5 then 0 else if x == 6 then 0 else if x == 7 then 0 else 0 }
     let r := Fetch () s
     (resultView r.1, (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat,
      [deltaView (r.2.c_update 7), deltaView (r.2.c_update 8)],
      (rawReadData 0 r.2).toNat,
      (List.range 16).map (fun j => (r.2.c_tlb 7 (BitVec.ofNat 4 j)).map tlbView),
      r.2.exception == exception.NoException, (r.2.MEM8 a).toNat,
      r.2.totalCore, r.2.procID.toNat)) =
      ((2, 0, 1656), 99, 99, [(true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8), (true, true, 11, (16, 48879), some 21, some 22, some 23, some 24, some 8)], 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], true, 3, 1, 7) := by
  simp only [modelFetchShape]
  repeat' apply Prod.ext
  all_goals simp [fetchExpected, singletonWord, writeFullWord, lookupEmpty, insertEmpty, resultView, deltaView, tlbView, fetchedDelta, PC,
    rawReadInst, boolify8, «write'Skip», translateAddr, MCSR, vmType, privilege,
    translate64, curASID, ASID_SIZE, SCSR, TLB, «write'TLB»,
    mkTLBEntry, lookupTLB, TLBEntries, Flapjack.holFor, walk64, rawReadData,
    MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE»,
    checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract,
    holUpdate, List.range_succ, List.map] <;> decide

end Flapjack.Test
