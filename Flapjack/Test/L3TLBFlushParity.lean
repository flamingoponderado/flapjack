import Flapjack.RiscV.L3.Defs.MMU.Flush
set_option maxRecDepth 200000
namespace Flapjack.Test.L3TLBFlushParity
open Flapjack.RiscV.L3
/-! Flapjack-only original regression guards. Retained entries keep arbitrary
unobserved fields; SFENCE preserves all native fields outside only c_tlb. -/
private def table (base : TLBEntry) : BitVec 4 → Option TLBEntry :=
  let e := { base with asid := 3, global := false, vAddr := 0, vMatchMask := 4095 }
  fun j => if j == 3 then none else if j == 1 then some { e with global := true }
    else if j == 2 then some { e with asid := 4 } else if j == 4 then some { e with vAddr := 4096 }
    else if j == 0 || j == 14 || j == 15 then some e else none
private noncomputable def tableObservation (tab r : BitVec 4 → Option TLBEntry) := by
  classical
  exact ((List.range 16).map (fun i => (r (BitVec.ofNat 4 i)).isSome),
    (List.range 16).map (fun i => if (r (BitVec.ofNat 4 i)).isSome then
      decide (r (BitVec.ofNat 4 i) = tab (BitVec.ofNat 4 i)) else true))
private def fixture (base : riscv_state) (entry : TLBEntry) (asid addr core : Nat) : riscv_state :=
  { base with procID := BitVec.ofNat 8 core, totalCore := 1, c_tlb := fun _ => table entry, c_gpr := fun _ reg => if reg == 2 then BitVec.ofNat 64 addr else 99, c_SCSR := fun id => { base.c_SCSR id with sasid := BitVec.ofNat 64 asid } }
private noncomputable def observation (rs : BitVec 5) (s : riscv_state) := by
  classical
  exact let t := «dfn'SFENCE_VM» rs s
    (tableObservation (s.c_tlb s.procID) (t.c_tlb s.procID),
      decide (t.c_tlb (s.procID+1) = s.c_tlb (s.procID+1)),
      decide ({ t with c_tlb := s.c_tlb } = s),t.totalCore,t.procID.toNat)
-- Original flush_asid0_addrnone; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (0,none,table entry)) =
      ([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid0_addr0; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (0,(some (BitVec.ofNat 64 0)),table entry)) =
      ([false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid0_addr1; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (0,(some (BitVec.ofNat 64 1)),table entry)) =
      ([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid0_addr4096; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (0,(some (BitVec.ofNat 64 4096)),table entry)) =
      ([false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid3_addrnone; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (3,none,table entry)) =
      ([false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid3_addr0; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (3,(some (BitVec.ofNat 64 0)),table entry)) =
      ([false,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid3_addr1; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (3,(some (BitVec.ofNat 64 1)),table entry)) =
      ([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid3_addr4096; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (3,(some (BitVec.ofNat 64 4096)),table entry)) =
      ([false,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid4_addrnone; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (4,none,table entry)) =
      ([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid4_addr0; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (4,(some (BitVec.ofNat 64 0)),table entry)) =
      ([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid4_addr1; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (4,(some (BitVec.ofNat 64 1)),table entry)) =
      ([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid4_addr4096; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (4,(some (BitVec.ofNat 64 4096)),table entry)) =
      ([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid63_addrnone; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (63,none,table entry)) =
      ([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid63_addr0; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (63,(some (BitVec.ofNat 64 0)),table entry)) =
      ([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid63_addr1; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (63,(some (BitVec.ofNat 64 1)),table entry)) =
      ([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original flush_asid63_addr4096; source-derived independent filtering result.
example (entry : TLBEntry) :
    tableObservation (table entry) (flushTLB (63,(some (BitVec.ofNat 64 4096)),table entry)) =
      ([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs0_addr0_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 0 0 7) =
      (([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs0_addr0_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 0 0 255) =
      (([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs0_addr1_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 0 1 7) =
      (([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs0_addr1_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 0 1 255) =
      (([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs0_addr4096_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 0 4096 7) =
      (([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs0_addr4096_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 0 4096 255) =
      (([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs2_addr0_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 0 0 7) =
      (([false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs2_addr0_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 0 0 255) =
      (([false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs2_addr1_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 0 1 7) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs2_addr1_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 0 1 255) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs2_addr4096_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 0 4096 7) =
      (([false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid0_rs2_addr4096_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 0 4096 255) =
      (([false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs0_addr0_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 3 0 7) =
      (([false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs0_addr0_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 3 0 255) =
      (([false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs0_addr1_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 3 1 7) =
      (([false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs0_addr1_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 3 1 255) =
      (([false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs0_addr4096_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 3 4096 7) =
      (([false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs0_addr4096_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 3 4096 255) =
      (([false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs2_addr0_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 3 0 7) =
      (([false,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs2_addr0_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 3 0 255) =
      (([false,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs2_addr1_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 3 1 7) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs2_addr1_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 3 1 255) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs2_addr4096_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 3 4096 7) =
      (([false,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid3_rs2_addr4096_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 3 4096 255) =
      (([false,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs0_addr0_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 4 0 7) =
      (([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs0_addr0_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 4 0 255) =
      (([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs0_addr1_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 4 1 7) =
      (([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs0_addr1_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 4 1 255) =
      (([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs0_addr4096_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 4 4096 7) =
      (([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs0_addr4096_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 4 4096 255) =
      (([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs2_addr0_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 4 0 7) =
      (([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs2_addr0_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 4 0 255) =
      (([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs2_addr1_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 4 1 7) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs2_addr1_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 4 1 255) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs2_addr4096_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 4 4096 7) =
      (([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid4_rs2_addr4096_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 4 4096 255) =
      (([true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs0_addr0_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 63 0 7) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs0_addr0_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 63 0 255) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs0_addr1_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 63 1 7) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs0_addr1_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 63 1 255) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs0_addr4096_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 63 4096 7) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs0_addr4096_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 0 (fixture base entry 63 4096 255) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs2_addr0_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 63 0 7) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs2_addr0_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 63 0 255) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs2_addr1_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 63 1 7) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs2_addr1_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 63 1 255) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs2_addr4096_core7; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 63 4096 7) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,7) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

-- Original sfence_asid63_rs2_addr4096_core255; full original state frame.
example (base : riscv_state) (entry : TLBEntry) :
    observation 2 (fixture base entry 63 4096 255) =
      (([true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),true,true,1,255) := by
  simp [observation,fixture,tableObservation,table,flushTLB,«dfn'SFENCE_VM»,
    curASID,holWordExtract,ASID_SIZE,SCSR,TLB,«write'TLB»,GPR,gpr,TLBEntries,Flapjack.holFor,
    holUpdate,List.range_succ,List.map]

end Flapjack.Test.L3TLBFlushParity
