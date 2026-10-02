import Flapjack.RiscV.L3.Defs.MMU.Insert
namespace Flapjack.Test
open Flapjack.RiscV.L3
set_option maxRecDepth 200000

-- Original oracle insert_empty; all sixteen slots observed.
example : (let e := (fun age : BitVec 64 => { (default : TLBEntry) with asid := 1, age := age }); let t := addToTLB ((63:BitVec 6), (0:BitVec 64), (0:BitVec 64), «rec'SV_PTE» 0, (0:BitVec 64), 0, true, fun j => none) { (default : riscv_state) with procID := 7, totalCore := 1, c_cycles := fun _ => 77 }; (List.range 16).map (fun j => (t (BitVec.ofNat 4 j)).map (fun entry => (entry.asid.toNat, entry.age.toNat)))) =
    [some (63, 77), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] := by
  simp [addToTLB, TLBEntries, Flapjack.holFor, holUpdate, mkTLBEntry, LEVEL_BITS, PAGESIZE_BITS] <;> decide

-- Original oracle insert_holes; all sixteen slots observed.
example : (let e := (fun age : BitVec 64 => { (default : TLBEntry) with asid := 1, age := age }); let t := addToTLB ((63:BitVec 6), (0:BitVec 64), (0:BitVec 64), «rec'SV_PTE» 0, (0:BitVec 64), 0, true, fun j => if j == (2:BitVec 4) || j == (6:BitVec 4) then none else some (e 5)) { (default : riscv_state) with procID := 7, totalCore := 1, c_cycles := fun _ => 77 }; (List.range 16).map (fun j => (t (BitVec.ofNat 4 j)).map (fun entry => (entry.asid.toNat, entry.age.toNat)))) =
    [some (1, 5), some (1, 5), some (63, 77), some (1, 5), some (1, 5), some (1, 5), none, some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5)] := by
  simp [addToTLB, TLBEntries, Flapjack.holFor, holUpdate, mkTLBEntry, LEVEL_BITS, PAGESIZE_BITS] <;> decide

-- Original oracle insert_last_hole; all sixteen slots observed.
example : (let e := (fun age : BitVec 64 => { (default : TLBEntry) with asid := 1, age := age }); let t := addToTLB ((63:BitVec 6), (0:BitVec 64), (0:BitVec 64), «rec'SV_PTE» 0, (0:BitVec 64), 0, true, fun j => if j == (15:BitVec 4) then none else some (e 5)) { (default : riscv_state) with procID := 7, totalCore := 1, c_cycles := fun _ => 77 }; (List.range 16).map (fun j => (t (BitVec.ofNat 4 j)).map (fun entry => (entry.asid.toNat, entry.age.toNat)))) =
    [some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (63, 77)] := by
  simp [addToTLB, TLBEntries, Flapjack.holFor, holUpdate, mkTLBEntry, LEVEL_BITS, PAGESIZE_BITS] <;> decide

-- Original oracle insert_full_ascending; all sixteen slots observed.
example : (let e := (fun age : BitVec 64 => { (default : TLBEntry) with asid := 1, age := age }); let t := addToTLB ((63:BitVec 6), (0:BitVec 64), (0:BitVec 64), «rec'SV_PTE» 0, (0:BitVec 64), 0, true, fun j => some (e (j.zeroExtend 64))) { (default : riscv_state) with procID := 7, totalCore := 1, c_cycles := fun _ => 77 }; (List.range 16).map (fun j => (t (BitVec.ofNat 4 j)).map (fun entry => (entry.asid.toNat, entry.age.toNat)))) =
    [some (63, 77), some (1, 1), some (1, 2), some (1, 3), some (1, 4), some (1, 5), some (1, 6), some (1, 7), some (1, 8), some (1, 9), some (1, 10), some (1, 11), some (1, 12), some (1, 13), some (1, 14), some (1, 15)] := by
  simp [addToTLB, TLBEntries, Flapjack.holFor, holUpdate, mkTLBEntry, LEVEL_BITS, PAGESIZE_BITS] <;> decide

-- Original oracle insert_full_tie; all sixteen slots observed.
example : (let e := (fun age : BitVec 64 => { (default : TLBEntry) with asid := 1, age := age }); let t := addToTLB ((63:BitVec 6), (0:BitVec 64), (0:BitVec 64), «rec'SV_PTE» 0, (0:BitVec 64), 0, true, fun j => some (e 4)) { (default : riscv_state) with procID := 7, totalCore := 1, c_cycles := fun _ => 77 }; (List.range 16).map (fun j => (t (BitVec.ofNat 4 j)).map (fun entry => (entry.asid.toNat, entry.age.toNat)))) =
    [some (63, 77), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4), some (1, 4)] := by
  simp [addToTLB, TLBEntries, Flapjack.holFor, holUpdate, mkTLBEntry, LEVEL_BITS, PAGESIZE_BITS] <;> decide

-- Original oracle insert_full_max; all sixteen slots observed.
example : (let e := (fun age : BitVec 64 => { (default : TLBEntry) with asid := 1, age := age }); let t := addToTLB ((63:BitVec 6), (0:BitVec 64), (0:BitVec 64), «rec'SV_PTE» 0, (0:BitVec 64), 0, true, fun j => some (e 18446744073709551615)) { (default : riscv_state) with procID := 7, totalCore := 1, c_cycles := fun _ => 77 }; (List.range 16).map (fun j => (t (BitVec.ofNat 4 j)).map (fun entry => (entry.asid.toNat, entry.age.toNat)))) =
    [some (63, 77), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615), some (1, 18446744073709551615)] := by
  simp [addToTLB, TLBEntries, Flapjack.holFor, holUpdate, mkTLBEntry, LEVEL_BITS, PAGESIZE_BITS] <;> decide

-- Original oracle insert_last_oldest; all sixteen slots observed.
example : (let e := (fun age : BitVec 64 => { (default : TLBEntry) with asid := 1, age := age }); let t := addToTLB ((63:BitVec 6), (0:BitVec 64), (0:BitVec 64), «rec'SV_PTE» 0, (0:BitVec 64), 0, true, fun j => some (e (if j == (15:BitVec 4) then 0 else 5))) { (default : riscv_state) with procID := 7, totalCore := 1, c_cycles := fun _ => 77 }; (List.range 16).map (fun j => (t (BitVec.ofNat 4 j)).map (fun entry => (entry.asid.toNat, entry.age.toNat)))) =
    [some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (63, 77)] := by
  simp [addToTLB, TLBEntries, Flapjack.holFor, holUpdate, mkTLBEntry, LEVEL_BITS, PAGESIZE_BITS] <;> decide

-- Original oracle insert_early_oldest; all sixteen slots observed.
example : (let e := (fun age : BitVec 64 => { (default : TLBEntry) with asid := 1, age := age }); let t := addToTLB ((63:BitVec 6), (0:BitVec 64), (0:BitVec 64), «rec'SV_PTE» 0, (0:BitVec 64), 0, true, fun j => some (e (if j == (2:BitVec 4) then 0 else 5))) { (default : riscv_state) with procID := 7, totalCore := 1, c_cycles := fun _ => 77 }; (List.range 16).map (fun j => (t (BitVec.ofNat 4 j)).map (fun entry => (entry.asid.toNat, entry.age.toNat)))) =
    [some (1, 5), some (1, 5), some (63, 77), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5), some (1, 5)] := by
  simp [addToTLB, TLBEntries, Flapjack.holFor, holUpdate, mkTLBEntry, LEVEL_BITS, PAGESIZE_BITS] <;> decide

end Flapjack.Test
