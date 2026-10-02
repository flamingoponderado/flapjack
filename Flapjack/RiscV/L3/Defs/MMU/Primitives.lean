import Flapjack.RiscV.L3.Support

/-!
Complete original MMU constants, current-core CSR/TLB access, little-endian
physical word memory operations and SV record codecs. All fixed source word
widths are retained; each slice index is within its source dimension. These
primitives do not assemble walk64/translation, whose separate beads stay open.
-/
set_option maxRecDepth 200000
namespace Flapjack.RiscV.L3
open Flapjack.Basis.Pure.MlString

/-- HOL `riscv$privilege` (`privilege_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "privilege_def"]
noncomputable def privilege (p : (BitVec 2)) : Privilege :=
  (((fun (v : (BitVec 2)) => (if ((v == (BitVec.ofNat 2 0))) then Privilege.User else ((if ((v == (BitVec.ofNat 2 1))) then Privilege.Supervisor else ((if ((v == (BitVec.ofNat 2 2))) then Privilege.Hypervisor else ((if ((v == (BitVec.ofNat 2 3))) then Privilege.Machine else (Flapjack.holArb Privilege)))))))))) p)

/-- HOL `riscv$SCSR` (`SCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "SCSR_def"]
def SCSR (state : riscv_state) : SupervisorCSR :=
  (state.c_SCSR state.procID)

/-- HOL `riscv$ASID_SIZE` (`ASID_SIZE_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "ASID_SIZE_def"]
def ASID_SIZE  : Nat :=
  6

/-- HOL `riscv$reg'SV_PTE` (`reg'SV_PTE_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'SV_PTE_def"]
def «reg'SV_PTE» (x : SV_PTE) : (BitVec 64) :=
  (match x with | ⟨PTE_D, PTE_PPNi, PTE_R, PTE_SW, PTE_T, PTE_V, sv_pte_rst⟩ => (BitVec.setWidth 64 (sv_pte_rst ++ ((BitVec.setWidth 48 (PTE_PPNi ++ ((BitVec.setWidth 10 (PTE_SW ++ ((BitVec.setWidth 7 (((holV2w 1 ((PTE_D :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (((holV2w 1 ((PTE_R :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 (PTE_T ++ ((holV2w 1 ((PTE_V :: (([] : (List Bool)))))))))))))))))))))))))

/-- HOL `riscv$MEM` (`MEM_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "MEM_def"]
def MEM (a : (BitVec 61)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (let b : (BitVec 64) := ((BitVec.setWidth 64 a) <<< 3); (BitVec.setWidth 64 (((state.MEM8 ((b + (BitVec.ofNat 64 7))))) ++ ((BitVec.setWidth 56 (((state.MEM8 ((b + (BitVec.ofNat 64 6))))) ++ ((BitVec.setWidth 48 (((state.MEM8 ((b + (BitVec.ofNat 64 5))))) ++ ((BitVec.setWidth 40 (((state.MEM8 ((b + (BitVec.ofNat 64 4))))) ++ ((BitVec.setWidth 32 (((state.MEM8 ((b + (BitVec.ofNat 64 3))))) ++ ((BitVec.setWidth 24 (((state.MEM8 ((b + (BitVec.ofNat 64 2))))) ++ ((BitVec.setWidth 16 (((state.MEM8 ((b + (BitVec.ofNat 64 1))))) ++ (state.MEM8 b)))))))))))))))))))))))

/-- HOL `riscv$write'MEM` (`write'MEM_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'MEM_def"]
def «write'MEM» (arg0 : ((BitVec 64) × (BitVec 61))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (val, a) =>
  (fun (state : riscv_state) => (let b : (BitVec 64) := ((BitVec.setWidth 64 a) <<< 3); (let s : riscv_state := (let r := state; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 7))) (holWordExtract 8 63 56 val) state.MEM8)))) r.MEM8 }); (let s_1 : riscv_state := (let r := s; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 6))) (holWordExtract 8 55 48 val) s.MEM8)))) r.MEM8 }); (let s : riscv_state := (let r := s_1; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 5))) (holWordExtract 8 47 40 val) s_1.MEM8)))) r.MEM8 }); (let s_1 : riscv_state := (let r := s; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 4))) (holWordExtract 8 39 32 val) s.MEM8)))) r.MEM8 }); (let s : riscv_state := (let r := s_1; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 3))) (holWordExtract 8 31 24 val) s_1.MEM8)))) r.MEM8 }); (let s_1 : riscv_state := (let r := s; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 2))) (holWordExtract 8 23 16 val) s.MEM8)))) r.MEM8 }); (let s : riscv_state := (let r := s_1; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 1))) (holWordExtract 8 15 8 val) s_1.MEM8)))) r.MEM8 }); (let r := s; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate b (holWordExtract 8 7 0 val) s.MEM8)))) r.MEM8 }))))))))))

/-- HOL `riscv$TLB` (`TLB_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "TLB_def"]
def TLB (state : riscv_state) : ((BitVec 4) → (Option TLBEntry)) :=
  (state.c_tlb state.procID)

/-- HOL `riscv$write'TLB` (`write'TLB_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'TLB_def"]
def «write'TLB» (value : ((BitVec 4) → (Option TLBEntry))) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_tlb := ((fun (_eta1 : ((BitVec 8) → ((BitVec 4) → (Option TLBEntry)))) => (holUpdate state.procID value state.c_tlb))) r.c_tlb }))

/-- HOL `riscv$rec'SV_Vaddr` (`rec'SV_Vaddr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'SV_Vaddr_def"]
def «rec'SV_Vaddr» (x : (BitVec 64)) : SV_Vaddr :=
  (SV_Vaddr.mk (holWordExtract 12 11 0 x) (holWordExtract 36 47 12 x) (holWordExtract 16 63 48 x))

/-- HOL `riscv$LEVEL_BITS` (`LEVEL_BITS_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "LEVEL_BITS_def"]
def LEVEL_BITS  : Nat :=
  9

/-- HOL `riscv$rec'SV_PTE` (`rec'SV_PTE_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'SV_PTE_def"]
def «rec'SV_PTE» (x : (BitVec 64)) : SV_PTE :=
  (SV_PTE.mk (x.getLsbD 6) (holWordExtract 38 47 10 x) (x.getLsbD 5) (holWordExtract 3 9 7 x) (holWordExtract 4 4 1 x) (x.getLsbD 0) (holWordExtract 16 63 48 x))

/-- HOL `riscv$isGlobal` (`isGlobal_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "isGlobal_def"]
def isGlobal (perm : (BitVec 4)) : Bool :=
  ((holWordExtract 2 3 2 perm) == (BitVec.ofNat 2 3))

/-- HOL `riscv$PAGESIZE_BITS` (`PAGESIZE_BITS_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "PAGESIZE_BITS_def"]
def PAGESIZE_BITS  : Nat :=
  12

/-- HOL `riscv$TLBEntries` (`TLBEntries_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "TLBEntries_def"]
def TLBEntries  : Nat :=
  16


end Flapjack.RiscV.L3
