import Flapjack.RiscV.L3.Support
import Flapjack.Misc.BinaryIeeeRound
import Flapjack.Misc.BinaryIeeeConvert

/-!
# L3 RISC-V model: definitions

The definitions of `HOL/examples/l3-machine-code/riscv/model/riscvScript.sml` and
`HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml` reached from
`riscv_step$NextRISCV`, in dependency order, rendered by `scripts/hol_terms_to_lean.py` from the
elaborated HOL definition theorems that `scripts/l3/export_riscv_defs.sml` exports (the
committed export is `scripts/l3/riscv_defs.sexp.gz`). The type and constant renderings are the
tables of that script and `Flapjack/RiscV/L3/Support.lean`; HOL `bool` is Lean `Bool`, so HOL
`=` is `==` and quantifier-free conditions are Boolean.

Definitions that reach a constant without a rendering (the `machine_ieee` floating-point
operations, and through them `Run` and `NextRISCV`) are not emitted yet. Every
older emitted definition remains pending statement review; the eighteen FP comparison/conversion bodies
carry declaration-level qualified source reviews. Full dependency/transition acceptance remains
open. The rendering is mechanical, and agreement
with HOL is checked by parity probes, not proved.
-/

set_option maxRecDepth 200000

namespace Flapjack.RiscV.L3

open Flapjack.Basis.Pure.MlString

/-- HOL `riscv$PC` (`PC_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "PC_def"]
def PC (state : riscv_state) : (BitVec 64) :=
  (state.c_PC state.procID)

/-- HOL `riscv$MCSR` (`MCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "MCSR_def"]
def MCSR (state : riscv_state) : MachineCSR :=
  (state.c_MCSR state.procID)

/-- HOL `riscv$privilege` (`privilege_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "privilege_def"]
def privilege (p : (BitVec 2)) : Privilege :=
  (((fun (v : (BitVec 2)) => (if ((v == (BitVec.ofNat 2 0))) then Privilege.User else ((if ((v == (BitVec.ofNat 2 1))) then Privilege.Supervisor else ((if ((v == (BitVec.ofNat 2 2))) then Privilege.Hypervisor else ((if ((v == (BitVec.ofNat 2 3))) then Privilege.Machine else (holArb Privilege)))))))))) p)

/-- HOL `riscv$raise'exception` (`raise'exception_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "raise'exception_def"]
def «raise'exception» {Ta : Type} [Inhabited Ta] (e : exception) : (riscv_state → (Ta × riscv_state)) :=
  (fun (state : riscv_state) => ((holArb Ta), ((if (state.exception == exception.NoException) then ((let r := state; { r with exception := ((fun (_eta1 : exception) => e)) r.exception })) else state))))

/-- HOL `riscv$vmType` (`vmType_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "vmType_def"]
def vmType (vm : (BitVec 5)) : (riscv_state → (VM_Mode × riscv_state)) :=
  (fun (state : riscv_state) => (((fun (v : (BitVec 5)) => (if ((v == (BitVec.ofNat 5 0))) then (VM_Mode.Mbare, state) else ((if ((v == (BitVec.ofNat 5 1))) then (VM_Mode.Mbb, state) else ((if ((v == (BitVec.ofNat 5 2))) then (VM_Mode.Mbbid, state) else ((if ((v == (BitVec.ofNat 5 8))) then (VM_Mode.Sv32, state) else ((if ((v == (BitVec.ofNat 5 9))) then (VM_Mode.Sv39, state) else ((if ((v == (BitVec.ofNat 5 10))) then (VM_Mode.Sv48, state) else ((if ((v == (BitVec.ofNat 5 11))) then (VM_Mode.Sv57, state) else ((if ((v == (BitVec.ofNat 5 12))) then (VM_Mode.Sv64, state) else (((«raise'exception» (Ta := VM_Mode)) ((exception.UNDEFINED (((((BitVec.ofNat 8 85) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 107) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 111) :: (((BitVec.ofNat 8 119) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 100) :: (((BitVec.ofNat 8 100) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 115) :: (((BitVec.ofNat 8 115) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 115) :: (((BitVec.ofNat 8 108) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 105) :: (((BitVec.ofNat 8 111) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 109) :: (((BitVec.ofNat 8 111) :: (((BitVec.ofNat 8 100) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 58) :: (((BitVec.ofNat 8 32) :: (([] : (List HolChar))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ++ (holNumToDecString vm.toNat))))) state))))))))))))))))))) vm))

/-- HOL `riscv$SCSR` (`SCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "SCSR_def"]
def SCSR (state : riscv_state) : SupervisorCSR :=
  (state.c_SCSR state.procID)

/-- HOL `riscv$ASID_SIZE` (`ASID_SIZE_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "ASID_SIZE_def"]
def ASID_SIZE  : Nat :=
  6

/-- HOL `riscv$curASID` (`curASID_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "curASID_def"]
def curASID (_u_ : Unit) : (riscv_state → (BitVec 6)) :=
  (fun (state : riscv_state) => (holWordExtract 6 (ASID_SIZE - 1) 0 ((SCSR state).sasid)))

/-- HOL `riscv$checkMemPermission` (`checkMemPermission_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "checkMemPermission_def"]
def checkMemPermission (arg0 : (fetchType × (accessType × (Privilege × (BitVec 4))))) : (riscv_state → (Bool × riscv_state)) :=
  match arg0 with
  | (ft, (ac, (priv, perm))) =>
  (fun (state : riscv_state) => (((fun (v : (BitVec 4)) => (if ((v == (BitVec.ofNat 4 0))) then (((«raise'exception» (Ta := Bool)) ((exception.INTERNAL_ERROR (((BitVec.ofNat 8 67) :: (((BitVec.ofNat 8 104) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 99) :: (((BitVec.ofNat 8 107) :: (((BitVec.ofNat 8 105) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 103) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 112) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 109) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 111) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 80) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 103) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 45) :: (((BitVec.ofNat 8 84) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 98) :: (((BitVec.ofNat 8 108) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 112) :: (((BitVec.ofNat 8 111) :: (((BitVec.ofNat 8 105) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 33) :: (([] : (List HolChar))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) state)) else ((if ((v == (BitVec.ofNat 4 1))) then (((«raise'exception» (Ta := Bool)) ((exception.INTERNAL_ERROR (((BitVec.ofNat 8 67) :: (((BitVec.ofNat 8 104) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 99) :: (((BitVec.ofNat 8 107) :: (((BitVec.ofNat 8 105) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 103) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 112) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 109) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 111) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 80) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 103) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 45) :: (((BitVec.ofNat 8 84) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 98) :: (((BitVec.ofNat 8 108) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 112) :: (((BitVec.ofNat 8 111) :: (((BitVec.ofNat 8 105) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 33) :: (([] : (List HolChar))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) state)) else ((if ((v == (BitVec.ofNat 4 2))) then ((((if (priv == Privilege.User) then ((!(ac == accessType.Write))) else (((ac == accessType.Read) && (ft == fetchType.Data))))), state)) else ((if ((v == (BitVec.ofNat 4 3))) then (((((priv == Privilege.User) || ((!(ft == fetchType.Instruction))))), state)) else ((if ((v == (BitVec.ofNat 4 4))) then (((((ac == accessType.Read) && (ft == fetchType.Data))), state)) else ((if ((v == (BitVec.ofNat 4 5))) then ((((!(ft == fetchType.Instruction))), state)) else ((if ((v == (BitVec.ofNat 4 6))) then ((((!(ac == accessType.Write))), state)) else ((if ((v == (BitVec.ofNat 4 7))) then (true, state) else ((if ((v == (BitVec.ofNat 4 8))) then ((((((!(priv == Privilege.User))) && (((ac == accessType.Read) && (ft == fetchType.Data))))), state)) else ((if ((v == (BitVec.ofNat 4 9))) then ((((((!(priv == Privilege.User))) && ((!(ft == fetchType.Instruction))))), state)) else ((if ((v == (BitVec.ofNat 4 10))) then ((((((!(priv == Privilege.User))) && ((!(ac == accessType.Write))))), state)) else ((if ((v == (BitVec.ofNat 4 11))) then ((((!(priv == Privilege.User))), state)) else ((if ((v == (BitVec.ofNat 4 12))) then ((((((!(priv == Privilege.User))) && (((ac == accessType.Read) && (ft == fetchType.Data))))), state)) else ((if ((v == (BitVec.ofNat 4 13))) then ((((((!(priv == Privilege.User))) && ((!(ft == fetchType.Instruction))))), state)) else ((if ((v == (BitVec.ofNat 4 14))) then ((((((!(priv == Privilege.User))) && ((!(ac == accessType.Write))))), state)) else ((if ((v == (BitVec.ofNat 4 15))) then ((((!(priv == Privilege.User))), state)) else ((holArb (Bool × riscv_state)))))))))))))))))))))))))))))))))))) perm))

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

/-- HOL `riscv$rawWriteData` (`rawWriteData_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rawWriteData_def"]
def rawWriteData (arg0 : ((BitVec 64) × ((BitVec 64) × Nat))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (pAddr, (data, nbytes)) =>
  (fun (state : riscv_state) => (let mask : (BitVec 64) := (((((BitVec.setWidth 64 (BitVec.ofNat 1 1))) <<< (nbytes * 8))) - (BitVec.ofNat 64 1)); (let pAddrIdx : (BitVec 61) := (holWordExtract 61 63 3 pAddr); (let align : Nat := (holWordExtract 3 2 0 pAddr).toNat; (let v : (BitVec 64) := (MEM pAddrIdx state); (if (align == 0) then ((«write'MEM» ((((((v &&& (~~~mask))) ||| (data &&& mask))), pAddrIdx)) state)) else ((if ((decide ((align + nbytes) ≤ (64 / 8)))) then ((«write'MEM» ((((((v &&& ((~~~((mask <<< (align * 8))))))) ||| (((data &&& mask) <<< (align * 8))))), pAddrIdx)) state)) else ((let dw_mask : (BitVec 128) := ((BitVec.setWidth 128 mask) <<< (align * 8)); (let dw_new : (BitVec 128) := (((((BitVec.setWidth 128 (((MEM ((pAddrIdx + (BitVec.ofNat 61 1))) state)) ++ v))) &&& (~~~dw_mask))) ||| (((((BitVec.setWidth 128 data) <<< (align * 8))) &&& dw_mask))); («write'MEM» ((((holWordExtract 64 (64 - 1) 0 dw_new)), pAddrIdx)) ((«write'MEM» ((((holWordExtract 64 (((2 * 64) - 1)) 64 dw_new)), ((pAddrIdx + (BitVec.ofNat 61 1))))) state))))))))))))))

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

/-- HOL `riscv$rawReadData` (`rawReadData_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rawReadData_def"]
def rawReadData (pAddr : (BitVec 64)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (let pAddrIdx : (BitVec 61) := (holWordExtract 61 63 3 pAddr); (let align : Nat := (holWordExtract 3 2 0 pAddr).toNat; (if (align == 0) then (MEM pAddrIdx state) else ((holWordExtract 64 63 0 ((BitVec.sshiftRight ((BitVec.setWidth 128 (((MEM ((pAddrIdx + (BitVec.ofNat 61 1))) state)) ++ (MEM pAddrIdx state)))) (align * 8)))))))))

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

/-- HOL `riscv$walk64` (`walk64_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "walk64_def"]
def walk64 (arg0 : ((BitVec 64) × (fetchType × (accessType × (Privilege × ((BitVec 64) × Nat)))))) (state : riscv_state) : ((Option ((BitVec 64) × (SV_PTE × (Nat × (Bool × (BitVec 64)))))) × riscv_state) :=
  match arg0 with
  | (vAddr, (ft, (ac, (priv, (ptb, level))))) =>
  (let va : SV_Vaddr := («rec'SV_Vaddr» vAddr); (let pte_addr : (BitVec 64) := (ptb + ((((BitVec.setWidth 64 ((holWordExtract 9 (LEVEL_BITS - 1) 0 ((va.Sv_VPNi >>> (level * LEVEL_BITS))))))) <<< 3))); (let v : SV_PTE := («rec'SV_PTE» (rawReadData pte_addr state)); (if (!v.PTE_V) then ((((none : (Option ((BitVec 64) × (SV_PTE × (Nat × (Bool × (BitVec 64)))))))), state)) else ((if ((((v.PTE_T == (BitVec.ofNat 4 0))) || ((v.PTE_T == (BitVec.ofNat 4 1))))) then ((if (level == 0) then ((((none : (Option ((BitVec 64) × (SV_PTE × (Nat × (Bool × (BitVec 64)))))))), state)) else ((walk64 ((vAddr, ((ft, ((ac, ((priv, ((((BitVec.setWidth 64 (v.PTE_PPNi <<< PAGESIZE_BITS))), (level - 1))))))))))) state)))) else ((match (checkMemPermission ((ft, ((ac, (priv, v.PTE_T))))) state) with | (v0, s) => (if (!v0) then ((((none : (Option ((BitVec 64) × (SV_PTE × (Nat × (Bool × (BitVec 64)))))))), s)) else ((match (let s0 : SV_PTE := (let r := v; { r with PTE_R := ((fun (_eta1 : Bool) => true)) r.PTE_R }); (let s0_1 : SV_PTE := (if (ac == accessType.Write) then ((let r := s0; { r with PTE_D := ((fun (_eta1 : Bool) => true)) r.PTE_D })) else s0); (((some ((((BitVec.setWidth 64 ((BitVec.setWidth 50 (((if ((decide (level > 0))) then ((((BitVec.setWidth 38 ((((v.PTE_PPNi >>> (level * LEVEL_BITS))) <<< (level * LEVEL_BITS))))) ||| ((BitVec.setWidth 38 ((va.Sv_VPNi &&& (((((BitVec.ofNat 36 1) <<< (level * LEVEL_BITS))) - (BitVec.ofNat 36 1))))))))) else v.PTE_PPNi)) ++ va.Sv_PgOfs))))), ((s0_1, ((level, (((isGlobal v.PTE_T), pte_addr)))))))))), ((s0_1, ((if ((((!(v.PTE_R == s0_1.PTE_R))) || ((!(v.PTE_D == s0_1.PTE_D))))) then ((rawWriteData ((pte_addr, (((«reg'SV_PTE» s0_1), 8)))) s)) else s))))))) with | (r, s1) => (r, s1.2))))))))))))
termination_by arg0.2.2.2.2.2
decreasing_by simp_wf; simp_all only [beq_iff_eq]; omega

/-- HOL `riscv$mkTLBEntry` (`mkTLBEntry_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "mkTLBEntry_def"]
def mkTLBEntry (arg0 : ((BitVec 6) × (Bool × ((BitVec 64) × ((BitVec 64) × (SV_PTE × (Nat × (BitVec 64)))))))) : (riscv_state → TLBEntry) :=
  match arg0 with
  | (asid, (global, (vAddr, (pAddr, (pte, (i, pteAddr)))))) =>
  (fun (state : riscv_state) => (let s0 : TLBEntry := (let r := ((let r := ((let r := ((let r := ((let r := (holArb TLBEntry); { r with asid := ((fun (_eta1 : (BitVec 6)) => asid)) r.asid })); { r with global := ((fun (_eta1 : Bool) => global)) r.global })); { r with pte := ((fun (_eta1 : SV_PTE) => pte)) r.pte })); { r with pteAddr := ((fun (_eta1 : (BitVec 64)) => pteAddr)) r.pteAddr })); { r with vAddrMask := ((fun (_eta1 : (BitVec 64)) => (((((BitVec.ofNat 64 1) <<< (((LEVEL_BITS * i) + PAGESIZE_BITS)))) - (BitVec.ofNat 64 1))))) r.vAddrMask }); (let s0_1 : TLBEntry := (let r := s0; { r with vMatchMask := ((fun (_eta1 : (BitVec 64)) => ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))) ^^^ s0.vAddrMask)))) r.vMatchMask }); (let r := ((let r := ((let r := s0_1; { r with vAddr := ((fun (_eta1 : (BitVec 64)) => (vAddr &&& s0_1.vMatchMask))) r.vAddr })); { r with pAddr := ((fun (_eta1 : (BitVec 64)) => ((((BitVec.sshiftRight pAddr ((PAGESIZE_BITS + (LEVEL_BITS * i))))) <<< ((PAGESIZE_BITS + (LEVEL_BITS * i))))))) r.pAddr })); { r with age := ((fun (_eta1 : (BitVec 64)) => (state.c_cycles state.procID))) r.age }))))

/-- HOL `riscv$TLBEntries` (`TLBEntries_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "TLBEntries_def"]
def TLBEntries  : Nat :=
  16

/-- HOL `riscv$addToTLB` (`addToTLB_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "addToTLB_def"]
def addToTLB (arg0 : ((BitVec 6) × ((BitVec 64) × ((BitVec 64) × (SV_PTE × ((BitVec 64) × (Nat × (Bool × ((BitVec 4) → (Option TLBEntry)))))))))) : (riscv_state → ((BitVec 4) → (Option TLBEntry))) :=
  match arg0 with
  | (asid, (vAddr, (pAddr, (pte, (pteAddr, (i, (global, curTLB))))))) =>
  (fun (state : riscv_state) => (let s : (Bool × (Nat × ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state))))) := (((holFor ((0, (((TLBEntries - 1), ((fun (i_1 : Nat) => (fun (state_1 : (Bool × (Nat × ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state)))))) => (match (state_1.2.2.2.1 (BitVec.ofNat 4 i_1)) with | none => ((), ((if (!state_1.1) then ((true, ((let s0 : (Nat × ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state)))) := state_1.2; (s0.1, ((let s0_1 : ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state))) := s0.2; (s0_1.1, ((((holUpdate (BitVec.ofNat 4 i_1) (some state_1.2.2.2.2.1) state_1.2.2.2.1)), s0_1.2.2)))))))))) else state_1))) | some e => (if (BitVec.ult e.age state_1.2.2.1) then ((let s : (Bool × (Nat × ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state))))) := (state_1.1, ((let s : (Nat × ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state)))) := state_1.2; (s.1, (e.age, s.2.2))))); ((), ((s.1, (i_1, s.2.2)))))) else (((), state_1)))))))))))) ((false, ((0, ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))), ((curTLB, ((((mkTLBEntry ((asid, ((global, ((vAddr, ((pAddr, ((pte, (i, pteAddr))))))))))) state)), state)))))))))))).2; (if (!s.1) then ((holUpdate (BitVec.ofNat 4 s.2.1) (some s.2.2.2.2.1) s.2.2.2.1)) else s.2.2.2.1)))

/-- HOL `riscv$lookupTLB` (`lookupTLB_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lookupTLB_def"]
def lookupTLB (arg0 : ((BitVec 6) × ((BitVec 64) × ((BitVec 4) → (Option TLBEntry))))) : (Option (TLBEntry × (BitVec 4))) :=
  match arg0 with
  | (asid, (vAddr, tlb)) =>
  ((((holFor ((0, (((TLBEntries - 1), ((fun (i : Nat) => (fun (state : ((Option (TLBEntry × (BitVec 4))) × Unit)) => (match (tlb (BitVec.ofNat 4 i)) with | none => ((), state) | some e => ((), ((if ((((state.1 == ((none : (Option (TLBEntry × (BitVec 4))))))) && ((((e.global || (e.asid == asid))) && ((e.vAddr == (vAddr &&& e.vMatchMask))))))) then ((((some ((e, (BitVec.ofNat 4 i))))), ())) else state)))))))))))) ((((none : (Option (TLBEntry × (BitVec 4))))), ())))).2).1

/-- HOL `riscv$translate64` (`translate64_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "translate64_def"]
def translate64 (arg0 : ((BitVec 64) × (fetchType × (accessType × (Privilege × Nat))))) : (riscv_state → ((Option (BitVec 64)) × riscv_state)) :=
  match arg0 with
  | (vAddr, (ft, (ac, (priv, level)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 6) := (curASID () state); (match (lookupTLB ((v, ((vAddr, (TLB state)))))) with | none => (match (walk64 ((vAddr, ((ft, ((ac, ((priv, ((((SCSR state).sptbr), level)))))))))) state) with | (v0, s) => (match v0 with | none => (((none : (Option (BitVec 64)))), s) | some v1 => (match v1 with | (pAddr, v3) => (match v3 with | (pte, v5) => (match v5 with | (i, v7) => (match v7 with | (global, pteAddr) => ((some pAddr), ((«write'TLB» ((addToTLB ((v, ((vAddr, ((pAddr, ((pte, ((pteAddr, ((i, ((global, (TLB s))))))))))))))) s)) s))))))))) | some v2 => (match v2 with | (e, idx) => (match (checkMemPermission ((ft, ((ac, (priv, e.pte.PTE_T))))) state) with | (v_1, s) => (if v_1 then ((((some ((e.pAddr ||| (vAddr &&& e.vAddrMask))))), ((if (((ac == accessType.Write) && (!e.pte.PTE_D))) then ((let s0 : TLBEntry := (let r := e; { r with pte := ((fun (_eta1 : SV_PTE) => ((let r := e.pte; { r with PTE_D := ((fun (_eta1 : Bool) => true)) r.PTE_D })))) r.pte }); (let s1 : riscv_state := (rawWriteData ((s0.pteAddr, (((«reg'SV_PTE» s0.pte), 8)))) s); («write'TLB» ((holUpdate idx (some s0) (TLB s1))) s1)))) else s)))) else ((((none : (Option (BitVec 64)))), s))))))))

/-- HOL `riscv$translateAddr` (`translateAddr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "translateAddr_def"]
def translateAddr (arg0 : ((BitVec 64) × (fetchType × accessType))) : (riscv_state → ((Option (BitVec 64)) × riscv_state)) :=
  match arg0 with
  | (vAddr, (ft, ac)) =>
  (fun (state : riscv_state) => (let v : Privilege := (privilege ((if (((((MCSR state).mstatus).MMPRV) && (ft == fetchType.Data))) then (((MCSR state).mstatus).MPRV1) else (((MCSR state).mstatus).MPRV)))); (match (match (vmType (((MCSR state).mstatus).VM) state) with | (v0, s) => ((v0, v), s)) with | (v0, s) => (match v0 with | (v1, v2) => (match v1 with | .Mbare => ((some vAddr), s) | .Mbb => (match v2 with | .User => (((none : (Option (BitVec 64)))), s) | .Supervisor => (((none : (Option (BitVec 64)))), s) | .Hypervisor => (((none : (Option (BitVec 64)))), s) | .Machine => ((some vAddr), s)) | .Mbbid => (match v2 with | .User => (((none : (Option (BitVec 64)))), s) | .Supervisor => (((none : (Option (BitVec 64)))), s) | .Hypervisor => (((none : (Option (BitVec 64)))), s) | .Machine => ((some vAddr), s)) | .Sv32 => (match v2 with | .User => (((none : (Option (BitVec 64)))), s) | .Supervisor => (((none : (Option (BitVec 64)))), s) | .Hypervisor => (((none : (Option (BitVec 64)))), s) | .Machine => ((some vAddr), s)) | .Sv39 => (match v2 with | .User => (translate64 ((vAddr, ((ft, ((ac, (v, 2))))))) s) | .Supervisor => (translate64 ((vAddr, ((ft, ((ac, (v, 2))))))) s) | .Hypervisor => (translate64 ((vAddr, ((ft, ((ac, (v, 2))))))) s) | .Machine => ((some vAddr), s)) | .Sv48 => (match v2 with | .User => (translate64 ((vAddr, ((ft, ((ac, (v, 3))))))) s) | .Supervisor => (translate64 ((vAddr, ((ft, ((ac, (v, 3))))))) s) | .Hypervisor => (translate64 ((vAddr, ((ft, ((ac, (v, 3))))))) s) | .Machine => ((some vAddr), s)) | .Sv57 => (match v2 with | .User => (((none : (Option (BitVec 64)))), s) | .Supervisor => (((none : (Option (BitVec 64)))), s) | .Hypervisor => (((none : (Option (BitVec 64)))), s) | .Machine => ((some vAddr), s)) | .Sv64 => (match v2 with | .User => (((none : (Option (BitVec 64)))), s) | .Supervisor => (((none : (Option (BitVec 64)))), s) | .Hypervisor => (((none : (Option (BitVec 64)))), s) | .Machine => ((some vAddr), s)))))))

/-- HOL `riscv$boolify8` (`boolify8_def`), generated by `bitstringLib.bitify_boolify` for an L3 `BL` call (no source declaration); mechanically rendered from the elaborated HOL definition. Flapjack infrastructure, untagged. -/
def boolify8 (w : (BitVec 8)) : (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))))) :=
  ((w.getLsbD 7), (((w.getLsbD 6), (((w.getLsbD 5), (((w.getLsbD 4), (((w.getLsbD 3), (((w.getLsbD 2), (((w.getLsbD 1), (w.getLsbD 0))))))))))))))

/-- HOL `riscv$write'Skip` (`write'Skip_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'Skip_def"]
def «write'Skip» (value : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_Skip := ((fun (_eta1 : ((BitVec 8) → (BitVec 64))) => (holUpdate state.procID value state.c_Skip))) r.c_Skip }))

/-- HOL `riscv$rawReadInst` (`rawReadInst_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rawReadInst_def"]
def rawReadInst (pAddr : (BitVec 64)) : (riscv_state → (rawInstType × riscv_state)) :=
  (fun (state : riscv_state) => (match (boolify8 (state.MEM8 pAddr)) with | (_b_7, _b_6, _b_5, _b_4, _b_3, _b_2, b_1, b_0) => (if (b_1 && b_0) then ((let s : riscv_state := («write'Skip» (BitVec.ofNat 64 4) state); (((rawInstType.Word ((BitVec.setWidth 32 (((s.MEM8 ((pAddr + (BitVec.ofNat 64 3))))) ++ ((BitVec.setWidth 24 (((s.MEM8 ((pAddr + (BitVec.ofNat 64 2))))) ++ ((BitVec.setWidth 16 (((s.MEM8 ((pAddr + (BitVec.ofNat 64 1))))) ++ (s.MEM8 pAddr)))))))))))), s))) else ((let s : riscv_state := («write'Skip» (BitVec.ofNat 64 2) state); (((rawInstType.Half ((BitVec.setWidth 16 (((s.MEM8 ((pAddr + (BitVec.ofNat 64 1))))) ++ (s.MEM8 pAddr)))))), s))))))

/-- HOL `riscv_step$Fetch` (`Fetch_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "Fetch_def"]
noncomputable def Fetch (s : riscv_state) : (rawInstType × riscv_state) :=
  (match (translateAddr (((PC s), (fetchType.Instruction, accessType.Read))) s) with | (w, s_1) => (rawReadInst (holThe w) s_1))

/-- HOL `riscv$boolify32` (`boolify32_def`), generated by `bitstringLib.bitify_boolify` for an L3 `BL` call (no source declaration); mechanically rendered from the elaborated HOL definition. Flapjack infrastructure, untagged. -/
def boolify32 (w : (BitVec 32)) : (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))))))))))))))))))))))))))))) :=
  ((w.getLsbD 31), (((w.getLsbD 30), (((w.getLsbD 29), (((w.getLsbD 28), (((w.getLsbD 27), (((w.getLsbD 26), (((w.getLsbD 25), (((w.getLsbD 24), (((w.getLsbD 23), (((w.getLsbD 22), (((w.getLsbD 21), (((w.getLsbD 20), (((w.getLsbD 19), (((w.getLsbD 18), (((w.getLsbD 17), (((w.getLsbD 16), (((w.getLsbD 15), (((w.getLsbD 14), (((w.getLsbD 13), (((w.getLsbD 12), (((w.getLsbD 11), (((w.getLsbD 10), (((w.getLsbD 9), (((w.getLsbD 8), (((w.getLsbD 7), (((w.getLsbD 6), (((w.getLsbD 5), (((w.getLsbD 4), (((w.getLsbD 3), (((w.getLsbD 2), (((w.getLsbD 1), (w.getLsbD 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- HOL `riscv$asSImm12` (`asSImm12_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "asSImm12_def"]
def asSImm12 (arg0 : ((BitVec 7) × (BitVec 5))) : (BitVec 12) :=
  match arg0 with
  | (immhi, immlo) =>
  (BitVec.setWidth 12 (immhi ++ immlo))

/-- HOL `riscv$asImm20` (`asImm20_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "asImm20_def"]
def asImm20 (arg0 : ((BitVec 1) × ((BitVec 8) × ((BitVec 1) × (BitVec 10))))) : (BitVec 20) :=
  match arg0 with
  | (imm20, (immhi, (imm11, immlo))) =>
  (BitVec.setWidth 20 (imm20 ++ ((BitVec.setWidth 19 (immhi ++ ((BitVec.setWidth 11 (imm11 ++ immlo))))))))

/-- HOL `riscv$asImm12` (`asImm12_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "asImm12_def"]
def asImm12 (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 6) × (BitVec 4))))) : (BitVec 12) :=
  match arg0 with
  | (imm12, (imm11, (immhi, immlo))) =>
  (BitVec.setWidth 12 (imm12 ++ ((BitVec.setWidth 11 (imm11 ++ ((BitVec.setWidth 10 (immhi ++ immlo))))))))

/-- HOL `riscv$Decode` (`Decode_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Decode_def"]
def Decode (w : (BitVec 32)) : instruction :=
  (match (boolify32 w) with | (b_31, b_30, b_29, b_28, b_27, b_26, b_25, b_24, b_23, b_22, b_21, b_20, b_19, b_18, b_17, b_16, b_15, b_14, b_13, b_12, b_11, b_10, b_9, b_8, b_7, b_6, b_5, b_4, b_3, b_2, b_1, b_0) => (if b_6 then ((if (b_1 && b_0) then ((if (((!b_14) && (((!b_13) && (((!b_12) && ((b_5 && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Branch ((Branch.BEQ ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asImm12 ((((holV2w 1 ((b_31 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_7 :: (([] : (List Bool))))))), ((((holV2w 6 ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))), ((holV2w 4 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: (([] : (List Bool))))))))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && ((b_12 && ((b_5 && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Branch ((Branch.BNE ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asImm12 ((((holV2w 1 ((b_31 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_7 :: (([] : (List Bool))))))), ((((holV2w 6 ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))), ((holV2w 4 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: (([] : (List Bool))))))))))))))))))))))))))))) else ((if ((b_14 && (((!b_13) && (((!b_12) && ((b_5 && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Branch ((Branch.BLT ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asImm12 ((((holV2w 1 ((b_31 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_7 :: (([] : (List Bool))))))), ((((holV2w 6 ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))), ((holV2w 4 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: (([] : (List Bool))))))))))))))))))))))))))))) else ((if ((b_14 && (((!b_13) && ((b_12 && ((b_5 && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Branch ((Branch.BGE ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asImm12 ((((holV2w 1 ((b_31 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_7 :: (([] : (List Bool))))))), ((((holV2w 6 ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))), ((holV2w 4 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: (([] : (List Bool))))))))))))))))))))))))))))) else ((if ((b_14 && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Branch ((Branch.BLTU ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asImm12 ((((holV2w 1 ((b_31 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_7 :: (([] : (List Bool))))))), ((((holV2w 6 ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))), ((holV2w 4 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: (([] : (List Bool))))))))))))))))))))))))))))) else ((if ((b_14 && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Branch ((Branch.BGEU ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asImm12 ((((holV2w 1 ((b_31 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_7 :: (([] : (List Bool))))))), ((((holV2w 6 ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))), ((holV2w 4 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: (([] : (List Bool))))))))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_12) && ((b_5 && (((!b_4) && (((!b_3) && b_2)))))))))))) then ((instruction.Branch ((Branch.JALR ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if ((b_5 && (((!b_4) && (b_3 && b_2))))) then ((instruction.Branch ((Branch.JAL ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((asImm20 ((((holV2w 1 ((b_31 :: (([] : (List Bool))))))), ((((holV2w 8 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))), ((((holV2w 1 ((b_20 :: (([] : (List Bool))))))), ((holV2w 10 ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))))) else ((if (((!b_26) && (((!b_25) && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))) then ((instruction.FArith ((FArith.FMADD_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_26) && (((!b_25) && (((!b_5) && (((!b_4) && (((!b_3) && b_2)))))))))) then ((instruction.FArith ((FArith.FMSUB_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_26) && (((!b_25) && (((!b_5) && (((!b_4) && ((b_3 && (!b_2))))))))))) then ((instruction.FArith ((FArith.FNMSUB_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_26) && (((!b_25) && (((!b_5) && (((!b_4) && (b_3 && b_2))))))))) then ((instruction.FArith ((FArith.FNMADD_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))) then ((instruction.FArith ((FArith.FADD_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && ((b_27 && (((!b_26) && (((!b_25) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))) then ((instruction.FArith ((FArith.FSUB_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))) then ((instruction.FArith ((FArith.FMUL_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && ((b_27 && (((!b_26) && (((!b_25) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))) then ((instruction.FArith ((FArith.FDIV_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && ((b_28 && ((b_27 && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FSQRT_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && ((b_27 && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FMIN_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && ((b_27 && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FMAX_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if ((b_31 && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && ((b_13 && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FEQ_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if ((b_31 && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FLT_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if ((b_31 && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FLE_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FSGNJ_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FSGNJN_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && ((b_13 && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FSGNJX_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_W_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && ((b_20 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_WU_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FMV_X_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))))))))) else ((if ((b_31 && ((b_30 && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCLASS_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_S_W ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && ((b_20 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_S_WU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && ((b_29 && ((b_28 && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FMV_S_X ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_26) && ((b_25 && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))) then ((instruction.FArith ((FArith.FMADD_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_26) && ((b_25 && (((!b_5) && (((!b_4) && (((!b_3) && b_2)))))))))) then ((instruction.FArith ((FArith.FMSUB_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_26) && ((b_25 && (((!b_5) && (((!b_4) && ((b_3 && (!b_2))))))))))) then ((instruction.FArith ((FArith.FNMSUB_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_26) && ((b_25 && (((!b_5) && (((!b_4) && (b_3 && b_2))))))))) then ((instruction.FArith ((FArith.FNMADD_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))) then ((instruction.FArith ((FArith.FADD_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && ((b_27 && (((!b_26) && ((b_25 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))) then ((instruction.FArith ((FArith.FSUB_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && ((b_25 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))) then ((instruction.FArith ((FArith.FMUL_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && ((b_27 && (((!b_26) && ((b_25 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))) then ((instruction.FArith ((FArith.FDIV_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && ((b_28 && ((b_27 && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FSQRT_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && ((b_27 && (((!b_26) && ((b_25 && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FMIN_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && ((b_27 && (((!b_26) && ((b_25 && (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FMAX_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if ((b_31 && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && ((b_13 && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FEQ_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if ((b_31 && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FLT_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if ((b_31 && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FArith ((FArith.FLE_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FSGNJ_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FSGNJN_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && ((b_13 && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FSGNJX_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_W_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && ((b_20 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_WU_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCLASS_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_D_W ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && ((b_20 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_D_WU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && ((b_21 && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_L_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && ((b_21 && ((b_20 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_LU_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && ((b_21 && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_S_L ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && ((b_21 && ((b_20 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_S_LU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && ((b_21 && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_L_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && ((b_21 && ((b_20 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_LU_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && ((b_21 && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_D_L ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && ((b_21 && ((b_20 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_D_LU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if ((b_31 && ((b_30 && ((b_29 && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FMV_X_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))))))))) else ((if ((b_31 && ((b_30 && ((b_29 && ((b_28 && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FMV_D_X ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && ((b_20 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_S_D ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))) then ((instruction.FConv ((FConv.FCVT_D_S ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 3 ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.System ((System.CSRRW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.System ((System.CSRRS ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.System ((System.CSRRC ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if ((b_14 && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.System ((System.CSRRWI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if ((b_14 && ((b_13 && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.System ((System.CSRRSI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if ((b_14 && ((b_13 && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.System ((System.CSRRCI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_19) && (((!b_18) && (((!b_17) && (((!b_16) && (((!b_15) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))))))))))))))))))))))) then (instruction.System System.ECALL) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && ((b_20 && (((!b_19) && (((!b_18) && (((!b_17) && (((!b_16) && (((!b_15) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))))))))))))))))))))))) then (instruction.System System.EBREAK) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_19) && (((!b_18) && (((!b_17) && (((!b_16) && (((!b_15) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))))))))))))))))))))))) then (instruction.System System.ERET) else ((if (((!b_31) && (((!b_30) && ((b_29 && ((b_28 && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && ((b_22 && (((!b_21) && ((b_20 && (((!b_19) && (((!b_18) && (((!b_17) && (((!b_16) && (((!b_15) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))))))))))))))))))))))) then (instruction.System System.MRTS) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && ((b_21 && (((!b_20) && (((!b_19) && (((!b_18) && (((!b_17) && (((!b_16) && (((!b_15) && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))))))))))))))))))))))) then (instruction.System System.WFI) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && ((b_20 && (((!b_14) && (((!b_13) && (((!b_12) && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))))))))))))))))))))))) then ((instruction.System ((System.SFENCE_VM ((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))))))) else instruction.UnknownInstruction)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) else instruction.UnknownInstruction)) else ((if (b_1 && b_0) then ((if ((b_5 && ((b_4 && (((!b_3) && b_2)))))) then ((instruction.ArithI ((ArithI.LUI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((holV2w 20 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))))))))))))))))) else ((if (((!b_5) && ((b_4 && (((!b_3) && b_2)))))) then ((instruction.ArithI ((ArithI.AUIPC ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((holV2w 20 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: ((b_14 :: ((b_13 :: ((b_12 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.ArithI ((ArithI.ADDI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SLLI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 6 ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.ArithI ((ArithI.SLTI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.ArithI ((ArithI.SLTIU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if ((b_14 && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.ArithI ((ArithI.XORI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_14 && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SRLI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 6 ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_14 && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SRAI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 6 ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))) else ((if ((b_14 && ((b_13 && (((!b_12) && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.ArithI ((ArithI.ORI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if ((b_14 && ((b_13 && ((b_12 && (((!b_5) && ((b_4 && (((!b_3) && (!b_2))))))))))))) then ((instruction.ArithI ((ArithI.ANDI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.ArithR ((ArithR.ADD ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.ArithR ((ArithR.SUB ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SLL ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.ArithR ((ArithR.SLT ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.ArithR ((ArithR.SLTU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && ((b_14 && (((!b_13) && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.ArithR ((ArithR.XOR ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && ((b_14 && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SRL ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && ((b_14 && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SRA ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && ((b_14 && ((b_13 && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.ArithR ((ArithR.OR ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && ((b_14 && ((b_13 && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.ArithR ((ArithR.AND ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && ((b_4 && ((b_3 && (!b_2))))))))))))) then ((instruction.ArithI ((ArithI.ADDIW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SLLIW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && ((b_14 && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SRLIW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && ((b_14 && (((!b_13) && ((b_12 && (((!b_5) && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SRAIW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && (((!b_12) && ((b_5 && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.ArithR ((ArithR.ADDW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && (((!b_12) && ((b_5 && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.ArithR ((ArithR.SUBW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && (((!b_14) && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SLLW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && ((b_14 && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SRLW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && (((!b_25) && ((b_14 && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.Shift ((Shift.SRAW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && (((!b_13) && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.MUL ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.MULH ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.MULHSU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.MULHU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && ((b_14 && (((!b_13) && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.DIV ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && ((b_14 && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.DIVU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && ((b_14 && ((b_13 && (((!b_12) && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.REM ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && ((b_14 && ((b_13 && ((b_12 && ((b_5 && ((b_4 && (((!b_3) && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.REMU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && (((!b_14) && (((!b_13) && (((!b_12) && ((b_5 && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.MULW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && ((b_14 && (((!b_13) && (((!b_12) && ((b_5 && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.DIVW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && ((b_14 && (((!b_13) && ((b_12 && ((b_5 && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.DIVUW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && ((b_14 && ((b_13 && (((!b_12) && ((b_5 && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.REMW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_26) && ((b_25 && ((b_14 && ((b_13 && ((b_12 && ((b_5 && ((b_4 && ((b_3 && (!b_2))))))))))))))))))))))))))) then ((instruction.MulDiv ((MulDiv.REMUW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Load ((Load.LB ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Load ((Load.LH ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && (((!b_12) && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Load ((Load.LW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && ((b_12 && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Load ((Load.LD ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if ((b_14 && (((!b_13) && (((!b_12) && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Load ((Load.LBU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if ((b_14 && (((!b_13) && ((b_12 && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Load ((Load.LHU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if ((b_14 && ((b_13 && (((!b_12) && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Load ((Load.LWU ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_12) && ((b_5 && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Store ((Store.SB ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asSImm12 ((((holV2w 7 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))))), ((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && ((b_12 && ((b_5 && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Store ((Store.SH ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asSImm12 ((((holV2w 7 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))))), ((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Store ((Store.SW ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asSImm12 ((((holV2w 7 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))))), ((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then ((instruction.Store ((Store.SD ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asSImm12 ((((holV2w 7 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))))), ((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_12) && (((!b_5) && (((!b_4) && (b_3 && b_2))))))))))) then ((instruction.FENCE ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 4 ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: (([] : (List Bool))))))))))))), ((holV2w 4 ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && ((b_12 && (((!b_5) && (((!b_4) && (b_3 && b_2))))))))))) then ((instruction.FENCE_I ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && (((!b_12) && (((!b_5) && (((!b_4) && (((!b_3) && b_2)))))))))))) then ((instruction.FPLoad ((FPLoad.FLW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && ((b_12 && (((!b_5) && (((!b_4) && (((!b_3) && b_2)))))))))))) then ((instruction.FPLoad ((FPLoad.FLD ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 12 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (((!b_3) && b_2)))))))))))) then ((instruction.FPStore ((FPStore.FSW ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asSImm12 ((((holV2w 7 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))))), ((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (((!b_3) && b_2)))))))))))) then ((instruction.FPStore ((FPStore.FSD ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))), ((asSImm12 ((((holV2w 7 ((b_31 :: ((b_30 :: ((b_29 :: ((b_28 :: ((b_27 :: ((b_26 :: ((b_25 :: (([] : (List Bool))))))))))))))))))), ((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && (((!b_27) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))))))))))))) then ((instruction.AMO ((AMO.LR_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && (((!b_27) && (((!b_24) && (((!b_23) && (((!b_22) && (((!b_21) && (((!b_20) && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))))))))))))) then ((instruction.AMO ((AMO.LR_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && ((b_27 && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.SC_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && ((b_28 && ((b_27 && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.SC_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && ((b_27 && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOSWAP_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOADD_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOXOR_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && ((b_29 && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOAND_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOOR_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if ((b_31 && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOMIN_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if ((b_31 && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOMAX_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOMINU_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if ((b_31 && ((b_30 && ((b_29 && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && (((!b_12) && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOMAXU_W ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && ((b_27 && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOSWAP_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOADD_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOXOR_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && ((b_29 && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOAND_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_31) && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOOR_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if ((b_31 && (((!b_30) && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOMIN_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if ((b_31 && (((!b_30) && ((b_29 && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOMAX_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if ((b_31 && ((b_30 && (((!b_29) && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOMINU_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if ((b_31 && ((b_30 && ((b_29 && (((!b_28) && (((!b_27) && (((!b_14) && ((b_13 && ((b_12 && ((b_5 && (((!b_4) && (b_3 && b_2))))))))))))))))))))) then ((instruction.AMO ((AMO.AMOMAXU_D ((((holV2w 1 ((b_26 :: (([] : (List Bool))))))), ((((holV2w 1 ((b_25 :: (([] : (List Bool))))))), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((((holV2w 5 ((b_19 :: ((b_18 :: ((b_17 :: ((b_16 :: ((b_15 :: (([] : (List Bool))))))))))))))), ((holV2w 5 ((b_24 :: ((b_23 :: ((b_22 :: ((b_21 :: ((b_20 :: (([] : (List Bool))))))))))))))))))))))))))) else instruction.UnknownInstruction)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) else instruction.UnknownInstruction))))

/-- HOL `riscv$boolify16` (`boolify16_def`), generated by `bitstringLib.bitify_boolify` for an L3 `BL` call (no source declaration); mechanically rendered from the elaborated HOL definition. Flapjack infrastructure, untagged. -/
def boolify16 (w : (BitVec 16)) : (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))))))))))))) :=
  ((w.getLsbD 15), (((w.getLsbD 14), (((w.getLsbD 13), (((w.getLsbD 12), (((w.getLsbD 11), (((w.getLsbD 10), (((w.getLsbD 9), (((w.getLsbD 8), (((w.getLsbD 7), (((w.getLsbD 6), (((w.getLsbD 5), (((w.getLsbD 4), (((w.getLsbD 3), (((w.getLsbD 2), (((w.getLsbD 1), (w.getLsbD 0))))))))))))))))))))))))))))))

/-- HOL `riscv$DecodeRVC` (`DecodeRVC_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "DecodeRVC_def"]
def DecodeRVC (h : (BitVec 16)) : instruction :=
  (match (boolify16 h) with | (b_15, b_14, b_13, b_12, b_11, b_10, b_9, b_8, b_7, b_6, b_5, b_4, b_3, b_2, b_1, b_0) => (if b_15 then ((if b_0 then ((if (!b_1) then ((if (((!b_14) && (((!b_13) && (((!b_11) && (!b_10))))))) then ((let r : (BitVec 3) := (holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))); (instruction.Shift ((Shift.SRLI ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((BitVec.setWidth 6 (((holV2w 1 ((b_12 :: (([] : (List Bool))))))) ++ ((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_11) && b_10)))))) then ((let r : (BitVec 3) := (holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))); (instruction.Shift ((Shift.SRAI ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((BitVec.setWidth 6 (((holV2w 1 ((b_12 :: (([] : (List Bool))))))) ++ ((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && ((b_11 && (!b_10))))))) then ((let r : (BitVec 3) := (holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))); (instruction.ArithI ((ArithI.ANDI ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((BitVec.setWidth 12 (((holWordReplicate 7 7 ((holV2w 1 ((b_12 :: (([] : (List Bool))))))))) ++ ((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_12) && ((b_11 && ((b_10 && (((!b_6) && (!b_5))))))))))))) then ((let r : (BitVec 3) := (holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))); (instruction.ArithR ((ArithR.SUB ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_12) && ((b_11 && ((b_10 && (((!b_6) && b_5)))))))))))) then ((let r : (BitVec 3) := (holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))); (instruction.ArithR ((ArithR.XOR ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_12) && ((b_11 && ((b_10 && ((b_6 && (!b_5))))))))))))) then ((let r : (BitVec 3) := (holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))); (instruction.ArithR ((ArithR.OR ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && (((!b_12) && ((b_11 && ((b_10 && (b_6 && b_5))))))))))) then ((let r : (BitVec 3) := (holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))); (instruction.ArithR ((ArithR.AND ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && ((b_12 && ((b_11 && ((b_10 && (((!b_6) && (!b_5))))))))))))) then ((let r : (BitVec 3) := (holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))); (instruction.ArithR ((ArithR.SUBW ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_14) && (((!b_13) && ((b_12 && ((b_11 && ((b_10 && (((!b_6) && b_5)))))))))))) then ((let r : (BitVec 3) := (holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))); (instruction.ArithR ((ArithR.ADDW ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ r))), ((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_14) && b_13)) then ((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), ((BitVec.setWidth 20 (((holWordReplicate 10 10 ((holV2w 1 ((b_12 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 10 (((holV2w 1 ((b_8 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 9 (((holV2w 2 ((b_10 :: ((b_9 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 7 (((holV2w 1 ((b_6 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (((holV2w 1 ((b_7 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 (((holV2w 1 ((b_2 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 4 (((holV2w 1 ((b_11 :: (([] : (List Bool))))))) ++ ((holV2w 3 ((b_5 :: ((b_4 :: ((b_3 :: (([] : (List Bool)))))))))))))))))))))))))))))))))))))) else ((if ((b_14 && (!b_13))) then ((instruction.Branch ((Branch.BEQ ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))), (((BitVec.ofNat 5 0), ((BitVec.setWidth 12 (((holWordReplicate 5 5 ((holV2w 1 ((b_12 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 7 (((holV2w 2 ((b_6 :: ((b_5 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 5 (((holV2w 1 ((b_2 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 4 (((holV2w 2 ((b_11 :: ((b_10 :: (([] : (List Bool))))))))) ++ ((holV2w 2 ((b_4 :: ((b_3 :: (([] : (List Bool))))))))))))))))))))))))))))) else ((if (b_14 && b_13) then ((instruction.Branch ((Branch.BNE ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))), (((BitVec.ofNat 5 0), ((BitVec.setWidth 12 (((holWordReplicate 5 5 ((holV2w 1 ((b_12 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 7 (((holV2w 2 ((b_6 :: ((b_5 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 5 (((holV2w 1 ((b_2 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 4 (((holV2w 2 ((b_11 :: ((b_10 :: (([] : (List Bool))))))))) ++ ((holV2w 2 ((b_4 :: ((b_3 :: (([] : (List Bool))))))))))))))))))))))))))))) else instruction.UnknownInstruction)))))))))))))))))))))))) else instruction.UnknownInstruction)) else ((if b_14 then ((if (((!b_13) && (!b_1))) then ((instruction.Store ((Store.SW ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool)))))))))))))), ((BitVec.setWidth 12 ((BitVec.ofNat 5 0) ++ ((BitVec.setWidth 7 (((holV2w 1 ((b_5 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (((holV2w 3 ((b_12 :: ((b_11 :: ((b_10 :: (([] : (List Bool))))))))))) ++ ((BitVec.setWidth 3 (((holV2w 1 ((b_6 :: (([] : (List Bool))))))) ++ (BitVec.ofNat 2 0))))))))))))))))))))) else ((if ((b_13 && (!b_1))) then ((instruction.Store ((Store.SD ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool)))))))))))))), ((BitVec.setWidth 12 ((BitVec.ofNat 4 0) ++ ((BitVec.setWidth 8 (((holV2w 2 ((b_6 :: ((b_5 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 6 (((holV2w 3 ((b_12 :: ((b_11 :: ((b_10 :: (([] : (List Bool))))))))))) ++ (BitVec.ofNat 3 0)))))))))))))))))) else ((if (((!b_13) && b_1)) then ((instruction.Store ((Store.SW (((BitVec.ofNat 5 2), ((((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))), ((BitVec.setWidth 12 ((BitVec.ofNat 4 0) ++ ((BitVec.setWidth 8 (((holV2w 2 ((b_8 :: ((b_7 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 6 (((holV2w 4 ((b_12 :: ((b_11 :: ((b_10 :: ((b_9 :: (([] : (List Bool))))))))))))) ++ (BitVec.ofNat 2 0)))))))))))))))))) else ((if (b_13 && b_1) then ((instruction.Store ((Store.SD (((BitVec.ofNat 5 2), ((((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))), ((BitVec.setWidth 12 ((BitVec.ofNat 3 0) ++ ((BitVec.setWidth 9 (((holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))) ++ ((BitVec.setWidth 6 (((holV2w 3 ((b_12 :: ((b_11 :: ((b_10 :: (([] : (List Bool))))))))))) ++ (BitVec.ofNat 3 0)))))))))))))))))) else instruction.UnknownInstruction)))))))) else ((if ((b_13 && (!b_1))) then ((instruction.FPStore ((FPStore.FSD ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool)))))))))))))), ((BitVec.setWidth 12 ((BitVec.ofNat 4 0) ++ ((BitVec.setWidth 8 (((holV2w 2 ((b_6 :: ((b_5 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 6 (((holV2w 3 ((b_12 :: ((b_11 :: ((b_10 :: (([] : (List Bool))))))))))) ++ (BitVec.ofNat 3 0)))))))))))))))))) else ((if (((!b_13) && (((!b_12) && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && (((!b_6) && (((!b_5) && (((!b_4) && (((!b_3) && (((!b_2) && b_1)))))))))))))))))))))))) then instruction.UnknownInstruction else ((if (((!b_13) && (((!b_12) && (((!b_6) && (((!b_5) && (((!b_4) && (((!b_3) && (((!b_2) && b_1)))))))))))))) then ((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 0), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), (BitVec.ofNat 12 0))))))))) else ((if (((!b_13) && (((!b_12) && b_1)))) then ((instruction.ArithR ((ArithR.ADD ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), (((BitVec.ofNat 5 0), ((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))) else ((if (((!b_13) && ((b_12 && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && (((!b_6) && (((!b_5) && (((!b_4) && (((!b_3) && (((!b_2) && b_1)))))))))))))))))))))))) then (instruction.System System.EBREAK) else ((if (((!b_13) && ((b_12 && (((!b_6) && (((!b_5) && (((!b_4) && (((!b_3) && (((!b_2) && b_1)))))))))))))) then ((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 1), ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), (BitVec.ofNat 12 0))))))))) else ((if (((!b_13) && (b_12 && b_1))) then ((let r : (BitVec 5) := (holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))); (instruction.ArithR ((ArithR.ADD ((r, ((r, ((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool)))))))))))))))))))))))) else ((if (b_13 && b_1) then ((instruction.FPStore ((FPStore.FSD (((BitVec.ofNat 5 2), ((((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))), ((BitVec.setWidth 12 ((BitVec.ofNat 3 0) ++ ((BitVec.setWidth 9 (((holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))) ++ ((BitVec.setWidth 6 (((holV2w 3 ((b_12 :: ((b_11 :: ((b_10 :: (([] : (List Bool))))))))))) ++ (BitVec.ofNat 3 0)))))))))))))))))) else instruction.UnknownInstruction)))))))))))))))))))) else ((if b_13 then ((if b_0 then ((if (!b_1) then ((if (!b_14) then ((let r : (BitVec 5) := (holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))); (instruction.ArithI ((ArithI.ADDIW ((r, ((r, ((BitVec.setWidth 12 (((holWordReplicate 7 7 ((holV2w 1 ((b_12 :: (([] : (List Bool))))))))) ++ ((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if ((b_14 && (((!b_12) && (((!b_11) && (((!b_10) && (((!b_9) && ((b_8 && (((!b_7) && (((!b_6) && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))))))))))))))) then instruction.UnknownInstruction else ((if ((b_14 && (((!b_11) && (((!b_10) && (((!b_9) && ((b_8 && (!b_7))))))))))) then ((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 2), (((BitVec.ofNat 5 2), ((BitVec.setWidth 12 (((holWordReplicate 3 3 ((holV2w 1 ((b_12 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 9 (((holV2w 2 ((b_4 :: ((b_3 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 7 (((holV2w 1 ((b_5 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (((holV2w 1 ((b_2 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 (((holV2w 1 ((b_6 :: (([] : (List Bool))))))) ++ (BitVec.ofNat 4 0)))))))))))))))))))))))) else ((if ((b_14 && (((!b_12) && (((!b_6) && (((!b_5) && (((!b_4) && (((!b_3) && (!b_2))))))))))))) then instruction.UnknownInstruction else ((if b_14 then ((instruction.ArithI ((ArithI.LUI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), ((BitVec.setWidth 20 (((holWordReplicate 15 15 ((holV2w 1 ((b_12 :: (([] : (List Bool))))))))) ++ ((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool)))))))))))))))))))))))) else instruction.UnknownInstruction)))))))))) else instruction.UnknownInstruction)) else ((if (((!b_14) && (!b_1))) then ((instruction.FPLoad ((FPLoad.FLD ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool)))))))))))))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))), ((BitVec.setWidth 12 ((BitVec.ofNat 4 0) ++ ((BitVec.setWidth 8 (((holV2w 2 ((b_6 :: ((b_5 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 6 (((holV2w 3 ((b_12 :: ((b_11 :: ((b_10 :: (([] : (List Bool))))))))))) ++ (BitVec.ofNat 3 0)))))))))))))))))) else ((if ((b_14 && (!b_1))) then ((instruction.Load ((Load.LD ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool)))))))))))))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))), ((BitVec.setWidth 12 ((BitVec.ofNat 4 0) ++ ((BitVec.setWidth 8 (((holV2w 2 ((b_6 :: ((b_5 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 6 (((holV2w 3 ((b_12 :: ((b_11 :: ((b_10 :: (([] : (List Bool))))))))))) ++ (BitVec.ofNat 3 0)))))))))))))))))) else ((if (((!b_14) && b_1)) then ((instruction.FPLoad ((FPLoad.FLD ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), (((BitVec.ofNat 5 2), ((BitVec.setWidth 12 ((BitVec.ofNat 3 0) ++ ((BitVec.setWidth 9 (((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))) ++ ((BitVec.setWidth 6 (((holV2w 1 ((b_12 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 (((holV2w 2 ((b_6 :: ((b_5 :: (([] : (List Bool))))))))) ++ (BitVec.ofNat 3 0))))))))))))))))))))) else ((if ((b_14 && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && b_1)))))))))))) then instruction.UnknownInstruction else ((if (b_14 && b_1) then ((instruction.Load ((Load.LD ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), (((BitVec.ofNat 5 2), ((BitVec.setWidth 12 ((BitVec.ofNat 3 0) ++ ((BitVec.setWidth 9 (((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))) ++ ((BitVec.setWidth 6 (((holV2w 1 ((b_12 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 (((holV2w 2 ((b_6 :: ((b_5 :: (([] : (List Bool))))))))) ++ (BitVec.ofNat 3 0))))))))))))))))))))) else instruction.UnknownInstruction)))))))))))) else ((if b_14 then ((if (((!b_1) && (!b_0))) then ((instruction.Load ((Load.LW ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool)))))))))))))), ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))), ((BitVec.setWidth 12 ((BitVec.ofNat 5 0) ++ ((BitVec.setWidth 7 (((holV2w 1 ((b_5 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (((holV2w 3 ((b_12 :: ((b_11 :: ((b_10 :: (([] : (List Bool))))))))))) ++ ((BitVec.setWidth 3 (((holV2w 1 ((b_6 :: (([] : (List Bool))))))) ++ (BitVec.ofNat 2 0))))))))))))))))))))) else ((if (((!b_1) && b_0)) then ((instruction.ArithI ((ArithI.ADDI ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), (((BitVec.ofNat 5 0), ((BitVec.setWidth 12 (((holWordReplicate 7 7 ((holV2w 1 ((b_12 :: (([] : (List Bool))))))))) ++ ((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool)))))))))))))))))))))))))) else ((if (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && ((b_1 && (!b_0))))))))))))) then instruction.UnknownInstruction else ((if ((b_1 && (!b_0))) then ((instruction.Load ((Load.LW ((((holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))))), (((BitVec.ofNat 5 2), ((BitVec.setWidth 12 ((BitVec.ofNat 4 0) ++ ((BitVec.setWidth 8 (((holV2w 2 ((b_3 :: ((b_2 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 6 (((holV2w 1 ((b_12 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 (((holV2w 3 ((b_6 :: ((b_5 :: ((b_4 :: (([] : (List Bool))))))))))) ++ (BitVec.ofNat 2 0))))))))))))))))))))) else instruction.UnknownInstruction)))))))) else ((if (((!b_12) && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && (((!b_6) && (((!b_5) && (((!b_1) && (!b_0))))))))))))))))))) then instruction.UnknownInstruction else ((if (((!b_1) && (!b_0))) then ((instruction.ArithI ((ArithI.ADDI ((((BitVec.setWidth 5 ((BitVec.ofNat 2 1) ++ ((holV2w 3 ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool)))))))))))))), (((BitVec.ofNat 5 2), ((BitVec.setWidth 12 ((BitVec.ofNat 2 0) ++ ((BitVec.setWidth 10 (((holV2w 4 ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool))))))))))))) ++ ((BitVec.setWidth 6 (((holV2w 2 ((b_12 :: ((b_11 :: (([] : (List Bool))))))))) ++ ((BitVec.setWidth 4 (((holV2w 1 ((b_5 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 3 (((holV2w 1 ((b_6 :: (([] : (List Bool))))))) ++ (BitVec.ofNat 2 0)))))))))))))))))))))))) else ((if (((!b_12) && (((!b_11) && (((!b_10) && (((!b_9) && (((!b_8) && (((!b_7) && (((!b_6) && (((!b_5) && (((!b_4) && (((!b_3) && (((!b_2) && (((!b_1) && b_0)))))))))))))))))))))))) then ((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) else ((if (((!b_1) && b_0)) then ((let r : (BitVec 5) := (holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))); (instruction.ArithI ((ArithI.ADDI ((r, ((r, ((BitVec.setWidth 12 (((holWordReplicate 7 7 ((holV2w 1 ((b_12 :: (([] : (List Bool))))))))) ++ ((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))))))) else ((if ((b_1 && (!b_0))) then ((let r : (BitVec 5) := (holV2w 5 ((b_11 :: ((b_10 :: ((b_9 :: ((b_8 :: ((b_7 :: (([] : (List Bool)))))))))))))); (instruction.Shift ((Shift.SLLI ((r, ((r, ((BitVec.setWidth 6 (((holV2w 1 ((b_12 :: (([] : (List Bool))))))) ++ ((holV2w 5 ((b_6 :: ((b_5 :: ((b_4 :: ((b_3 :: ((b_2 :: (([] : (List Bool))))))))))))))))))))))))))) else instruction.UnknownInstruction))))))))))))))))

/-- HOL `riscv_step$DecodeAny` (`DecodeAny_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "DecodeAny_def"]
def DecodeAny (f : rawInstType) : instruction :=
  (match f with | .Half h => (DecodeRVC h) | .Word w => (Decode w))

/-- HOL `riscv$write'NextFetch` (`write'NextFetch_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'NextFetch_def"]
def «write'NextFetch» (value : (Option TransferControl)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_NextFetch := ((fun (_eta1 : ((BitVec 8) → (Option TransferControl))) => (holUpdate state.procID value state.c_NextFetch))) r.c_NextFetch }))

/-- HOL `riscv$setTrap` (`setTrap_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "setTrap_def"]
def setTrap (arg0 : (ExceptionType × (Option (BitVec 64)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (e, badaddr) =>
  (fun (state : riscv_state) => («write'NextFetch» ((some ((TransferControl.Trap ((let r := ((let r := (holArb SynchronousTrap); { r with trap := ((fun (_eta1 : ExceptionType) => e)) r.trap })); { r with badaddr := ((fun (_eta1 : (Option (BitVec 64))) => badaddr)) r.badaddr })))))) state))

/-- HOL `riscv$signalException` (`signalException_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "signalException_def"]
def signalException (e : ExceptionType) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (setTrap ((e, ((none : (Option (BitVec 64)))))) state))

/-- HOL `riscv$dfn'UnknownInstruction` (`dfn'UnknownInstruction_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'UnknownInstruction_def"]
def «dfn'UnknownInstruction» (state : riscv_state) : riscv_state :=
  (signalException ExceptionType.Illegal_Instr state)

/-- HOL `riscv$gpr` (`gpr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "gpr_def"]
def gpr (n : (BitVec 5)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (state.c_gpr state.procID n))

/-- HOL `riscv$GPR` (`GPR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "GPR_def"]
def GPR (n : (BitVec 5)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (if ((n == (BitVec.ofNat 5 0))) then (BitVec.ofNat 64 0) else (gpr n state)))

/-- HOL `riscv$flushTLB` (`flushTLB_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "flushTLB_def"]
def flushTLB (arg0 : ((BitVec 6) × ((Option (BitVec 64)) × ((BitVec 4) → (Option TLBEntry))))) : ((BitVec 4) → (Option TLBEntry)) :=
  match arg0 with
  | (asid, (addr, curTLB)) =>
  ((((holFor ((0, (((TLBEntries - 1), ((fun (i : Nat) => (fun (state : (((BitVec 4) → (Option TLBEntry)) × Unit)) => (match (((state.1 (BitVec.ofNat 4 i))), addr) with | (v, v1) => (match v with | none => ((), state) | some e => (match v1 with | none => ((), ((if ((((asid == (BitVec.ofNat 6 0))) || (((asid == e.asid) && (!e.global))))) then ((((holUpdate (BitVec.ofNat 4 i) ((none : (Option TLBEntry))) state.1)), ())) else state))) | some va => ((), ((if ((((((asid == (BitVec.ofNat 6 0))) || (((asid == e.asid) && (!e.global))))) && ((e.vAddr == (va &&& e.vMatchMask))))) then ((((holUpdate (BitVec.ofNat 4 i) ((none : (Option TLBEntry))) state.1)), ())) else state)))))))))))))) ((curTLB, ())))).2).1

/-- HOL `riscv$dfn'SFENCE_VM` (`dfn'SFENCE_VM_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SFENCE_VM_def"]
def «dfn'SFENCE_VM» (rs1 : (BitVec 5)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => («write'TLB» ((flushTLB ((((curASID () state)), ((((if ((rs1 == (BitVec.ofNat 5 0))) then ((none : (Option (BitVec 64)))) else ((some (GPR rs1 state))))), (TLB state))))))) state))

/-- HOL `riscv$write'SCSR` (`write'SCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'SCSR_def"]
def «write'SCSR» (value : SupervisorCSR) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_SCSR := ((fun (_eta1 : ((BitVec 8) → SupervisorCSR)) => (holUpdate state.procID value state.c_SCSR))) r.c_SCSR }))

/-- HOL `riscv$privLevel` (`privLevel_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "privLevel_def"]
def privLevel (p : Privilege) : (BitVec 2) :=
  (match p with | .User => (BitVec.ofNat 2 0) | .Supervisor => (BitVec.ofNat 2 1) | .Hypervisor => (BitVec.ofNat 2 2) | .Machine => (BitVec.ofNat 2 3))

/-- HOL `riscv$write'MCSR` (`write'MCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'MCSR_def"]
def «write'MCSR» (value : MachineCSR) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => (holUpdate state.procID value state.c_MCSR))) r.c_MCSR }))

/-- HOL `riscv$dfn'MRTS` (`dfn'MRTS_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'MRTS_def"]
def «dfn'MRTS» (state : riscv_state) : riscv_state :=
  (match (let s0 : riscv_state := («write'SCSR» ((let r := (SCSR state); { r with scause := ((fun (_eta1 : mcause) => ((MCSR state).mcause))) r.scause })) state); ((SCSR s0), s0)) with | (v, s) => (match (let s0 : riscv_state := («write'SCSR» ((let r := v; { r with sbadaddr := ((fun (_eta1 : (BitVec 64)) => ((MCSR s).mbadaddr))) r.sbadaddr })) s); ((SCSR s0), s0)) with | (v_1, s_1) => (match (let s0 : riscv_state := («write'SCSR» ((let r := v_1; { r with sepc := ((fun (_eta1 : (BitVec 64)) => ((MCSR s_1).mepc))) r.sepc })) s_1); ((MCSR s0), s0)) with | (v, s) => («write'NextFetch» (some TransferControl.Mrts) ((«write'MCSR» ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MPRV := ((fun (_eta1 : (BitVec 2)) => (privLevel Privilege.Supervisor))) r.MPRV })))) r.mstatus })) s))))))

/-- HOL `riscv$dfn'ERET` (`dfn'ERET_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ERET_def"]
def «dfn'ERET» (state : riscv_state) : riscv_state :=
  («write'NextFetch» (some TransferControl.Ereturn) state)

/-- HOL `riscv$signalEnvCall` (`signalEnvCall_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "signalEnvCall_def"]
def signalEnvCall (_u_ : Unit) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (signalException ((match (privilege (((MCSR state).mstatus).MPRV)) with | .User => ExceptionType.UMode_Env_Call | .Supervisor => ExceptionType.SMode_Env_Call | .Hypervisor => ExceptionType.HMode_Env_Call | .Machine => ExceptionType.MMode_Env_Call)) state))

/-- HOL `riscv$dfn'ECALL` (`dfn'ECALL_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ECALL_def"]
def «dfn'ECALL» (state : riscv_state) : riscv_state :=
  (signalEnvCall () state)

/-- HOL `riscv$dfn'EBREAK` (`dfn'EBREAK_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'EBREAK_def"]
def «dfn'EBREAK» (state : riscv_state) : riscv_state :=
  (signalException ExceptionType.Breakpoint state)

/-- HOL `riscv$architecture` (`architecture_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "architecture_def"]
def architecture (ab : (BitVec 2)) : (riscv_state → (Architecture × riscv_state)) :=
  (fun (state : riscv_state) => (((fun (v : (BitVec 2)) => (if ((v == (BitVec.ofNat 2 0))) then (Architecture.RV32I, state) else ((if ((v == (BitVec.ofNat 2 2))) then (Architecture.RV64I, state) else ((if ((v == (BitVec.ofNat 2 3))) then (Architecture.RV128I, state) else (((«raise'exception» (Ta := Architecture)) ((exception.UNDEFINED (((((BitVec.ofNat 8 85) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 107) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 111) :: (((BitVec.ofNat 8 119) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 99) :: (((BitVec.ofNat 8 104) :: (((BitVec.ofNat 8 105) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 99) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 117) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 58) :: (((BitVec.ofNat 8 32) :: (([] : (List HolChar))))))))))))))))))))))))))))))))))))))))))))))) ++ (holNumToDecString ab.toNat))))) state))))))))) ab))

/-- HOL `riscv$curArch` (`curArch_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "curArch_def"]
def curArch (_u_ : Unit) : (riscv_state → (Architecture × riscv_state)) :=
  (fun (state : riscv_state) => (architecture (((MCSR state).mcpuid).ArchBase) state))

/-- HOL `riscv$in32BitMode` (`in32BitMode_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "in32BitMode_def"]
def in32BitMode (_u_ : Unit) : (riscv_state → (Bool × riscv_state)) :=
  (fun (state : riscv_state) => (match (curArch () state) with | (v, s) => ((v == Architecture.RV32I), s)))

/-- HOL `riscv$is_CSR_defined` (`is_CSR_defined_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "is_CSR_defined_def"]
def is_CSR_defined (csr : (BitVec 12)) : (riscv_state → (Bool × riscv_state)) :=
  (fun (state : riscv_state) => (if ((((BitVec.sle (BitVec.ofNat 12 1) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 3))))) then (true, state) else ((if ((((BitVec.sle (BitVec.ofNat 12 3072) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 3074))))) then (true, state) else ((match (if ((BitVec.sle (BitVec.ofNat 12 3200) csr)) then ((if ((BitVec.sle csr (BitVec.ofNat 12 3202))) then ((in32BitMode () state)) else (false, state))) else (false, state)) with | (v, s) => (if v then (true, s) else ((if ((((BitVec.sle (BitVec.ofNat 12 256) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 257))))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 260))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 289))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 3329))) then (true, s) else ((match (if ((csr == (BitVec.ofNat 12 3457))) then ((in32BitMode () s)) else (false, s)) with | (v_1, s_1) => (if v_1 then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 320) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 321))))) then (true, s_1) else ((if ((csr == (BitVec.ofNat 12 324))) then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 3394) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 3395))))) then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 384) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 385))))) then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 2304) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 2306))))) then (true, s_1) else ((match (if ((BitVec.sle (BitVec.ofNat 12 2432) csr)) then ((if ((BitVec.sle csr (BitVec.ofNat 12 2434))) then ((in32BitMode () s_1)) else (false, s_1))) else (false, s_1)) with | (v, s) => (if v then (true, s) else ((if ((((BitVec.sle (BitVec.ofNat 12 3840) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 3841))))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 3856))) then (true, s) else ((if ((((BitVec.sle (BitVec.ofNat 12 768) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 770))))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 772))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 801))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 1793))) then (true, s) else ((match (if ((csr == (BitVec.ofNat 12 1857))) then ((in32BitMode () s)) else (false, s)) with | (v_1, s_1) => (if v_1 then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 832) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 836))))) then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 896) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 901))))) then (true, s_1) else ((if ((BitVec.sle (BitVec.ofNat 12 2817) csr)) then (true, s_1) else ((match (if ((csr == (BitVec.ofNat 12 2945))) then ((in32BitMode () s_1)) else (false, s_1)) with | (v, s) => (((v || ((((BitVec.sle (BitVec.ofNat 12 1920) csr)) && ((((BitVec.sle csr (BitVec.ofNat 12 1923))) && ((!((csr == (BitVec.ofNat 12 1922))))))))))), s)))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- HOL `riscv$curPrivilege` (`curPrivilege_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "curPrivilege_def"]
def curPrivilege (_u_ : Unit) : (riscv_state → Privilege) :=
  (fun (state : riscv_state) => (privilege (((MCSR state).mstatus).MPRV)))

/-- HOL `riscv$csrPR` (`csrPR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "csrPR_def"]
def csrPR (csr : (BitVec 12)) : (BitVec 2) :=
  (holWordExtract 2 9 8 csr)

/-- HOL `riscv$csrRW` (`csrRW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "csrRW_def"]
def csrRW (csr : (BitVec 12)) : (BitVec 2) :=
  (holWordExtract 2 11 10 csr)

/-- HOL `riscv$check_CSR_access` (`check_CSR_access_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "check_CSR_access_def"]
def check_CSR_access (arg0 : ((BitVec 2) × ((BitVec 2) × (Privilege × accessType)))) : Bool :=
  match arg0 with
  | (rw, (pr, (p, a))) =>
  ((((a == accessType.Read) || ((!((rw == (BitVec.ofNat 2 3))))))) && ((!(BitVec.ult (privLevel p) pr))))

/-- HOL `riscv$checkCSROp` (`checkCSROp_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "checkCSROp_def"]
def checkCSROp (arg0 : ((BitVec 12) × ((BitVec 5) × accessType))) : (riscv_state → (Bool × riscv_state)) :=
  match arg0 with
  | (csr, (_rs1, a)) =>
  (fun (state : riscv_state) => (match (is_CSR_defined csr state) with | (v, s) => (((v && ((check_CSR_access (((csrRW csr), (((csrPR csr), ((((curPrivilege () s)), a)))))))))), s)))

/-- HOL `riscv$reg'mip` (`reg'mip_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mip_def"]
def «reg'mip» (x : mip) : (BitVec 64) :=
  (match x with | ⟨HSIP, HTIP, MSIP, MTIP, SSIP, STIP, mip_rst⟩ => (BitVec.setWidth 64 ((holWordExtract 56 55 0 mip_rst) ++ ((BitVec.setWidth 8 (((holV2w 1 ((MTIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 7 (((holV2w 1 ((HTIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (((holV2w 1 ((STIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 ((holWordExtract 1 56 56 mip_rst) ++ ((BitVec.setWidth 4 (((holV2w 1 ((MSIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 3 (((holV2w 1 ((HSIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 2 (((holV2w 1 ((SSIP :: (([] : (List Bool))))))) ++ (holWordExtract 1 57 57 mip_rst)))))))))))))))))))))))))

/-- HOL `riscv$reg'mcause` (`reg'mcause_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mcause_def"]
def «reg'mcause» (x : mcause) : (BitVec 64) :=
  (match x with | ⟨EC, Int, mcause_rst⟩ => (BitVec.setWidth 64 (((holV2w 1 ((Int :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 63 (mcause_rst ++ EC))))))

/-- HOL `riscv$reg'mie` (`reg'mie_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mie_def"]
def «reg'mie» (x : mie) : (BitVec 64) :=
  (match x with | ⟨HSIE, HTIE, MSIE, MTIE, SSIE, STIE, mie_rst⟩ => (BitVec.setWidth 64 ((holWordExtract 56 55 0 mie_rst) ++ ((BitVec.setWidth 8 (((holV2w 1 ((MTIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 7 (((holV2w 1 ((HTIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (((holV2w 1 ((STIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 ((holWordExtract 1 56 56 mie_rst) ++ ((BitVec.setWidth 4 (((holV2w 1 ((MSIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 3 (((holV2w 1 ((HSIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 2 (((holV2w 1 ((SSIE :: (([] : (List Bool))))))) ++ (holWordExtract 1 57 57 mie_rst)))))))))))))))))))))))))

/-- HOL `riscv$reg'mtdeleg` (`reg'mtdeleg_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mtdeleg_def"]
def «reg'mtdeleg» (x : mtdeleg) : (BitVec 64) :=
  (match x with | ⟨Exc_deleg, Intr_deleg⟩ => (BitVec.setWidth 64 (Intr_deleg ++ Exc_deleg)))

/-- HOL `riscv$reg'mstatus` (`reg'mstatus_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mstatus_def"]
def «reg'mstatus» (x : mstatus) : (BitVec 64) :=
  (match x with | ⟨MFS, MIE, MIE1, MIE2, MIE3, MMPRV, MPRV, MPRV1, MPRV2, MPRV3, MSD, MXS, VM, mstatus_rst⟩ => (BitVec.setWidth 64 (((holV2w 1 ((MSD :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 63 (mstatus_rst ++ ((BitVec.setWidth 22 (VM ++ ((BitVec.setWidth 17 (((holV2w 1 ((MMPRV :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 16 (MXS ++ ((BitVec.setWidth 14 (MFS ++ ((BitVec.setWidth 12 (MPRV3 ++ ((BitVec.setWidth 10 (((holV2w 1 ((MIE3 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 9 (MPRV2 ++ ((BitVec.setWidth 7 (((holV2w 1 ((MIE2 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (MPRV1 ++ ((BitVec.setWidth 4 (((holV2w 1 ((MIE1 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 3 (MPRV ++ ((holV2w 1 ((MIE :: (([] : (List Bool))))))))))))))))))))))))))))))))))))))))))))))

/-- HOL `riscv$reg'mimpid` (`reg'mimpid_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mimpid_def"]
def «reg'mimpid» (x : mimpid) : (BitVec 64) :=
  (match x with | ⟨RVImpl, RVSource⟩ => (BitVec.setWidth 64 (RVImpl ++ RVSource)))

/-- HOL `riscv$reg'mcpuid` (`reg'mcpuid_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mcpuid_def"]
def «reg'mcpuid» (x : mcpuid) : (BitVec 64) :=
  (match x with | ⟨ArchBase, I_, M, S_, U, mcpuid_rst⟩ => (BitVec.setWidth 64 (ArchBase ++ ((BitVec.setWidth 62 ((holWordExtract 41 40 0 mcpuid_rst) ++ ((BitVec.setWidth 21 (((holV2w 1 ((U :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 20 ((holWordExtract 1 41 41 mcpuid_rst) ++ ((BitVec.setWidth 19 (((holV2w 1 ((S_ :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 18 ((holWordExtract 5 46 42 mcpuid_rst) ++ ((BitVec.setWidth 13 (((holV2w 1 ((M :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 12 ((holWordExtract 3 49 47 mcpuid_rst) ++ ((BitVec.setWidth 9 (((holV2w 1 ((I_ :: (([] : (List Bool))))))) ++ (holWordExtract 8 57 50 mcpuid_rst))))))))))))))))))))))))))))

/-- HOL `riscv$rec'sip` (`rec'sip_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'sip_def"]
def «rec'sip» (x : (BitVec 64)) : sip :=
  (sip.mk (x.getLsbD 1) (x.getLsbD 5) ((BitVec.setWidth 62 ((holWordExtract 1 0 0 x) ++ ((BitVec.setWidth 61 ((holWordExtract 3 4 2 x) ++ (holWordExtract 58 63 6 x))))))))

/-- HOL `riscv$lift_mip_sip` (`lift_mip_sip_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lift_mip_sip_def"]
def lift_mip_sip (mip : mip) : sip :=
  (let r := ((let r := ((«rec'sip» (BitVec.ofNat 64 0))); { r with STIP := ((fun (_eta1 : Bool) => mip.STIP)) r.STIP })); { r with SSIP := ((fun (_eta1 : Bool) => mip.SSIP)) r.SSIP })

/-- HOL `riscv$reg'sip` (`reg'sip_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'sip_def"]
def «reg'sip» (x : sip) : (BitVec 64) :=
  (match x with | ⟨SSIP, STIP, sip_rst⟩ => (BitVec.setWidth 64 ((holWordExtract 58 57 0 sip_rst) ++ ((BitVec.setWidth 6 (((holV2w 1 ((STIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 ((holWordExtract 3 60 58 sip_rst) ++ ((BitVec.setWidth 2 (((holV2w 1 ((SSIP :: (([] : (List Bool))))))) ++ (holWordExtract 1 61 61 sip_rst)))))))))))))

/-- HOL `riscv$rec'sie` (`rec'sie_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'sie_def"]
def «rec'sie» (x : (BitVec 64)) : sie :=
  (sie.mk (x.getLsbD 1) (x.getLsbD 5) ((BitVec.setWidth 62 ((holWordExtract 1 0 0 x) ++ ((BitVec.setWidth 61 ((holWordExtract 3 4 2 x) ++ (holWordExtract 58 63 6 x))))))))

/-- HOL `riscv$lift_mie_sie` (`lift_mie_sie_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lift_mie_sie_def"]
def lift_mie_sie (mie : mie) : sie :=
  (let r := ((let r := ((«rec'sie» (BitVec.ofNat 64 0))); { r with STIE := ((fun (_eta1 : Bool) => mie.STIE)) r.STIE })); { r with SSIE := ((fun (_eta1 : Bool) => mie.SSIE)) r.SSIE })

/-- HOL `riscv$reg'sie` (`reg'sie_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'sie_def"]
def «reg'sie» (x : sie) : (BitVec 64) :=
  (match x with | ⟨SSIE, STIE, sie_rst⟩ => (BitVec.setWidth 64 ((holWordExtract 58 57 0 sie_rst) ++ ((BitVec.setWidth 6 (((holV2w 1 ((STIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 ((holWordExtract 3 60 58 sie_rst) ++ ((BitVec.setWidth 2 (((holV2w 1 ((SSIE :: (([] : (List Bool))))))) ++ (holWordExtract 1 61 61 sie_rst)))))))))))))

/-- HOL `riscv$rec'sstatus` (`rec'sstatus_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'sstatus_def"]
def «rec'sstatus» (x : (BitVec 64)) : sstatus :=
  (sstatus.mk (holWordExtract 2 13 12 x) (x.getLsbD 0) (x.getLsbD 16) (x.getLsbD 3) (x.getLsbD 4) (x.getLsbD 63) (holWordExtract 2 15 14 x) ((BitVec.setWidth 55 ((holWordExtract 2 2 1 x) ++ ((BitVec.setWidth 53 ((holWordExtract 7 11 5 x) ++ (holWordExtract 46 62 17 x))))))))

/-- HOL `riscv$extStatus` (`extStatus_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "extStatus_def"]
def extStatus (e : (BitVec 2)) : ExtStatus :=
  (((fun (v : (BitVec 2)) => (if ((v == (BitVec.ofNat 2 0))) then ExtStatus.Off else ((if ((v == (BitVec.ofNat 2 1))) then ExtStatus.Initial else ((if ((v == (BitVec.ofNat 2 2))) then ExtStatus.Clean else ((if ((v == (BitVec.ofNat 2 3))) then ExtStatus.Dirty else (holArb ExtStatus)))))))))) e)

/-- HOL `riscv$lift_mstatus_sstatus` (`lift_mstatus_sstatus_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lift_mstatus_sstatus_def"]
def lift_mstatus_sstatus (mst : mstatus) : sstatus :=
  (let r := ((let r := ((let r := ((let r := ((let r := ((let r := ((let r := ((«rec'sstatus» (BitVec.ofNat 64 0))); { r with SMPRV := ((fun (_eta1 : Bool) => mst.MMPRV)) r.SMPRV })); { r with SXS := ((fun (_eta1 : (BitVec 2)) => mst.MXS)) r.SXS })); { r with SFS := ((fun (_eta1 : (BitVec 2)) => mst.MFS)) r.SFS })); { r with SSD := ((fun (_eta1 : Bool) => (((((extStatus mst.MXS) == ExtStatus.Dirty)) || (((extStatus mst.MFS) == ExtStatus.Dirty)))))) r.SSD })); { r with SPS := ((fun (_eta1 : Bool) => ((!(((privilege mst.MPRV1) == Privilege.User)))))) r.SPS })); { r with SPIE := ((fun (_eta1 : Bool) => mst.MIE1)) r.SPIE })); { r with SIE := ((fun (_eta1 : Bool) => mst.MIE)) r.SIE })

/-- HOL `riscv$reg'sstatus` (`reg'sstatus_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'sstatus_def"]
def «reg'sstatus» (x : sstatus) : (BitVec 64) :=
  (match x with | ⟨SFS, SIE, SMPRV, SPIE, SPS, SSD, SXS, sstatus_rst⟩ => (BitVec.setWidth 64 (((holV2w 1 ((SSD :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 63 ((holWordExtract 46 45 0 sstatus_rst) ++ ((BitVec.setWidth 17 (((holV2w 1 ((SMPRV :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 16 (SXS ++ ((BitVec.setWidth 14 (SFS ++ ((BitVec.setWidth 12 ((holWordExtract 7 52 46 sstatus_rst) ++ ((BitVec.setWidth 5 (((holV2w 1 ((SPS :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 4 (((holV2w 1 ((SPIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 3 ((holWordExtract 2 54 53 sstatus_rst) ++ ((holV2w 1 ((SIE :: (([] : (List Bool))))))))))))))))))))))))))))))))))

/-- HOL `riscv$reg'FPCSR` (`reg'FPCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'FPCSR_def"]
def «reg'FPCSR» (x : FPCSR) : (BitVec 32) :=
  (match x with | ⟨DZ, FRM, NV, NX, OF, UF, fpcsr_rst⟩ => (BitVec.setWidth 32 (fpcsr_rst ++ ((BitVec.setWidth 8 (FRM ++ ((BitVec.setWidth 5 (((holV2w 1 ((NV :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 4 (((holV2w 1 ((DZ :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 3 (((holV2w 1 ((OF :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 2 (((holV2w 1 ((UF :: (([] : (List Bool))))))) ++ ((holV2w 1 ((NX :: (([] : (List Bool)))))))))))))))))))))))))

/-- HOL `riscv$CSRMap` (`CSRMap_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "CSRMap_def"]
def CSRMap (csr : (BitVec 12)) : (riscv_state → ((BitVec 64) × riscv_state)) :=
  (fun (state : riscv_state) => (((fun (v : (BitVec 12)) => (if ((v == (BitVec.ofNat 12 1))) then ((((BitVec.setWidth 64 ((holWordExtract 5 4 0 ((«reg'FPCSR» ((state.c_UCSR state.procID).fpcsr))))))), state)) else ((if ((v == (BitVec.ofNat 12 2))) then ((((BitVec.setWidth 64 (((state.c_UCSR state.procID).fpcsr).FRM))), state)) else ((if ((v == (BitVec.ofNat 12 3))) then ((((BitVec.setWidth 64 ((holWordExtract 8 7 0 ((«reg'FPCSR» ((state.c_UCSR state.procID).fpcsr))))))), state)) else ((if ((v == (BitVec.ofNat 12 3072))) then (((((state.c_cycles state.procID) + ((state.c_UCSR state.procID).cycle_delta))), state)) else ((if ((v == (BitVec.ofNat 12 3073))) then ((((state.clock + ((state.c_UCSR state.procID).time_delta))), state)) else ((if ((v == (BitVec.ofNat 12 3074))) then (((((state.c_instret state.procID) + ((state.c_UCSR state.procID).instret_delta))), state)) else ((if ((v == (BitVec.ofNat 12 3200))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 (((state.c_cycles state.procID) + ((state.c_UCSR state.procID).cycle_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 3201))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 ((state.clock + ((state.c_UCSR state.procID).time_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 3202))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 (((state.c_instret state.procID) + ((state.c_UCSR state.procID).instret_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 256))) then ((((«reg'sstatus» ((lift_mstatus_sstatus ((state.c_MCSR state.procID).mstatus))))), state)) else ((if ((v == (BitVec.ofNat 12 257))) then ((((state.c_SCSR state.procID).stvec), state)) else ((if ((v == (BitVec.ofNat 12 260))) then ((((«reg'sie» ((lift_mie_sie ((state.c_MCSR state.procID).mie))))), state)) else ((if ((v == (BitVec.ofNat 12 289))) then ((((state.c_SCSR state.procID).stimecmp), state)) else ((if ((v == (BitVec.ofNat 12 3329))) then ((((state.clock + ((state.c_SCSR state.procID).stime_delta))), state)) else ((if ((v == (BitVec.ofNat 12 3457))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 ((state.clock + ((state.c_SCSR state.procID).stime_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 320))) then ((((state.c_SCSR state.procID).sscratch), state)) else ((if ((v == (BitVec.ofNat 12 321))) then ((((state.c_SCSR state.procID).sepc), state)) else ((if ((v == (BitVec.ofNat 12 3394))) then ((((«reg'mcause» ((state.c_SCSR state.procID).scause))), state)) else ((if ((v == (BitVec.ofNat 12 3395))) then ((((state.c_SCSR state.procID).sbadaddr), state)) else ((if ((v == (BitVec.ofNat 12 324))) then ((((«reg'sip» ((lift_mip_sip ((state.c_MCSR state.procID).mip))))), state)) else ((if ((v == (BitVec.ofNat 12 384))) then ((((state.c_SCSR state.procID).sptbr), state)) else ((if ((v == (BitVec.ofNat 12 385))) then ((((state.c_SCSR state.procID).sasid), state)) else ((if ((v == (BitVec.ofNat 12 2304))) then (((((state.c_cycles state.procID) + ((state.c_UCSR state.procID).cycle_delta))), state)) else ((if ((v == (BitVec.ofNat 12 2305))) then ((((state.clock + ((state.c_UCSR state.procID).time_delta))), state)) else ((if ((v == (BitVec.ofNat 12 2306))) then (((((state.c_instret state.procID) + ((state.c_UCSR state.procID).instret_delta))), state)) else ((if ((v == (BitVec.ofNat 12 2432))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 (((state.c_cycles state.procID) + ((state.c_UCSR state.procID).cycle_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 2433))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 ((state.clock + ((state.c_UCSR state.procID).time_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 2434))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 (((state.c_instret state.procID) + ((state.c_UCSR state.procID).instret_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 512))) then ((((«reg'mstatus» ((state.c_HCSR state.procID).hstatus))), state)) else ((if ((v == (BitVec.ofNat 12 513))) then ((((state.c_HCSR state.procID).htvec), state)) else ((if ((v == (BitVec.ofNat 12 514))) then ((((«reg'mtdeleg» ((state.c_HCSR state.procID).htdeleg))), state)) else ((if ((v == (BitVec.ofNat 12 545))) then ((((state.c_HCSR state.procID).htimecmp), state)) else ((if ((v == (BitVec.ofNat 12 3585))) then ((((state.clock + ((state.c_HCSR state.procID).htime_delta))), state)) else ((if ((v == (BitVec.ofNat 12 3713))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 ((state.clock + ((state.c_HCSR state.procID).htime_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 576))) then ((((state.c_HCSR state.procID).hscratch), state)) else ((if ((v == (BitVec.ofNat 12 577))) then ((((state.c_HCSR state.procID).hepc), state)) else ((if ((v == (BitVec.ofNat 12 578))) then ((((«reg'mcause» ((state.c_HCSR state.procID).hcause))), state)) else ((if ((v == (BitVec.ofNat 12 579))) then ((((state.c_HCSR state.procID).hbadaddr), state)) else ((if ((v == (BitVec.ofNat 12 2561))) then ((((state.clock + ((state.c_SCSR state.procID).stime_delta))), state)) else ((if ((v == (BitVec.ofNat 12 2689))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 ((state.clock + ((state.c_SCSR state.procID).stime_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 3840))) then ((((«reg'mcpuid» ((state.c_MCSR state.procID).mcpuid))), state)) else ((if ((v == (BitVec.ofNat 12 3841))) then ((((«reg'mimpid» ((state.c_MCSR state.procID).mimpid))), state)) else ((if ((v == (BitVec.ofNat 12 3856))) then ((((state.c_MCSR state.procID).mhartid), state)) else ((if ((v == (BitVec.ofNat 12 768))) then ((((«reg'mstatus» ((state.c_MCSR state.procID).mstatus))), state)) else ((if ((v == (BitVec.ofNat 12 769))) then ((((state.c_MCSR state.procID).mtvec), state)) else ((if ((v == (BitVec.ofNat 12 770))) then ((((«reg'mtdeleg» ((state.c_MCSR state.procID).mtdeleg))), state)) else ((if ((v == (BitVec.ofNat 12 772))) then ((((«reg'mie» ((state.c_MCSR state.procID).mie))), state)) else ((if ((v == (BitVec.ofNat 12 801))) then ((((state.c_MCSR state.procID).mtimecmp), state)) else ((if ((v == (BitVec.ofNat 12 1793))) then ((((state.clock + ((state.c_MCSR state.procID).mtime_delta))), state)) else ((if ((v == (BitVec.ofNat 12 1857))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 ((state.clock + ((state.c_MCSR state.procID).mtime_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 832))) then ((((state.c_MCSR state.procID).mscratch), state)) else ((if ((v == (BitVec.ofNat 12 833))) then ((((state.c_MCSR state.procID).mepc), state)) else ((if ((v == (BitVec.ofNat 12 834))) then ((((«reg'mcause» ((state.c_MCSR state.procID).mcause))), state)) else ((if ((v == (BitVec.ofNat 12 835))) then ((((state.c_MCSR state.procID).mbadaddr), state)) else ((if ((v == (BitVec.ofNat 12 836))) then ((((«reg'mip» ((state.c_MCSR state.procID).mip))), state)) else ((if ((v == (BitVec.ofNat 12 896))) then ((((state.c_MCSR state.procID).mbase), state)) else ((if ((v == (BitVec.ofNat 12 897))) then ((((state.c_MCSR state.procID).mbound), state)) else ((if ((v == (BitVec.ofNat 12 898))) then ((((state.c_MCSR state.procID).mibase), state)) else ((if ((v == (BitVec.ofNat 12 899))) then ((((state.c_MCSR state.procID).mibound), state)) else ((if ((v == (BitVec.ofNat 12 900))) then ((((state.c_MCSR state.procID).mdbase), state)) else ((if ((v == (BitVec.ofNat 12 901))) then ((((state.c_MCSR state.procID).mdbound), state)) else ((if ((v == (BitVec.ofNat 12 2817))) then ((((state.clock + ((state.c_HCSR state.procID).htime_delta))), state)) else ((if ((v == (BitVec.ofNat 12 2945))) then ((((BitVec.signExtend 64 ((holWordExtract 32 63 32 ((state.clock + ((state.c_HCSR state.procID).htime_delta))))))), state)) else ((if ((v == (BitVec.ofNat 12 1920))) then ((((state.c_MCSR state.procID).mtohost), state)) else ((if ((v == (BitVec.ofNat 12 1921))) then ((((state.c_MCSR state.procID).mfromhost), state)) else ((if ((v == (BitVec.ofNat 12 1923))) then (((BitVec.ofNat 64 0), state)) else (((«raise'exception» (Ta := (BitVec 64))) ((exception.UNDEFINED (((((BitVec.ofNat 8 117) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 120) :: (((BitVec.ofNat 8 112) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 99) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 100) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 67) :: (((BitVec.ofNat 8 83) :: (((BitVec.ofNat 8 82) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 100) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 32) :: (([] : (List HolChar))))))))))))))))))))))))))))))))))))))))))))))))) ++ (holWordToHexString csr))))) state))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) csr))

/-- HOL `riscv$CSR` (`CSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "CSR_def"]
def CSR (n : (BitVec 12)) : (riscv_state → ((BitVec 64) × riscv_state)) :=
  (fun (state : riscv_state) => (CSRMap n state))

/-- HOL `riscv$sendIPI` (`sendIPI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "sendIPI_def"]
def sendIPI (core : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let id : (BitVec 8) := (BitVec.setWidth 8 core); (if ((decide (id.toNat < state.totalCore))) then ((let v : MachineCSR := (state.c_MCSR id); (let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate id ((let r := v; { r with mip := ((fun (_eta1 : mip) => ((let r := v.mip; { r with MSIP := ((fun (_eta1 : Bool) => true)) r.MSIP })))) r.mip })) state.c_MCSR)))) r.c_MCSR }))) else state)))

/-- HOL `riscv$rec'mip` (`rec'mip_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mip_def"]
def «rec'mip» (x : (BitVec 64)) : mip :=
  (mip.mk (x.getLsbD 2) (x.getLsbD 6) (x.getLsbD 3) (x.getLsbD 7) (x.getLsbD 1) (x.getLsbD 5) ((BitVec.setWidth 58 ((holWordExtract 1 0 0 x) ++ ((BitVec.setWidth 57 ((holWordExtract 1 4 4 x) ++ (holWordExtract 56 63 8 x))))))))

/-- HOL `riscv$rec'mcause` (`rec'mcause_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mcause_def"]
def «rec'mcause» (x : (BitVec 64)) : mcause :=
  (mcause.mk (holWordExtract 4 3 0 x) (x.getLsbD 63) (holWordExtract 59 62 4 x))

/-- HOL `riscv$rec'mie` (`rec'mie_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mie_def"]
def «rec'mie» (x : (BitVec 64)) : mie :=
  (mie.mk (x.getLsbD 2) (x.getLsbD 6) (x.getLsbD 3) (x.getLsbD 7) (x.getLsbD 1) (x.getLsbD 5) ((BitVec.setWidth 58 ((holWordExtract 1 0 0 x) ++ ((BitVec.setWidth 57 ((holWordExtract 1 4 4 x) ++ (holWordExtract 56 63 8 x))))))))

/-- HOL `riscv$rec'mtdeleg` (`rec'mtdeleg_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mtdeleg_def"]
def «rec'mtdeleg» (x : (BitVec 64)) : mtdeleg :=
  (mtdeleg.mk (holWordExtract 16 15 0 x) (holWordExtract 48 63 16 x))

/-- HOL `riscv$rec'mstatus` (`rec'mstatus_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mstatus_def"]
def «rec'mstatus» (x : (BitVec 64)) : mstatus :=
  (mstatus.mk (holWordExtract 2 13 12 x) (x.getLsbD 0) (x.getLsbD 3) (x.getLsbD 6) (x.getLsbD 9) (x.getLsbD 16) (holWordExtract 2 2 1 x) (holWordExtract 2 5 4 x) (holWordExtract 2 8 7 x) (holWordExtract 2 11 10 x) (x.getLsbD 63) (holWordExtract 2 15 14 x) (holWordExtract 5 21 17 x) (holWordExtract 41 62 22 x))

/-- HOL `riscv$isValidVM` (`isValidVM_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "isValidVM_def"]
def isValidVM (vm : (BitVec 5)) : Bool :=
  (((fun (v : (BitVec 5)) => (if ((v == (BitVec.ofNat 5 0))) then true else ((if ((v == (BitVec.ofNat 5 1))) then true else ((if ((v == (BitVec.ofNat 5 2))) then true else ((if ((v == (BitVec.ofNat 5 8))) then true else ((if ((v == (BitVec.ofNat 5 9))) then true else ((if ((v == (BitVec.ofNat 5 10))) then true else ((if ((v == (BitVec.ofNat 5 11))) then true else ((if ((v == (BitVec.ofNat 5 12))) then true else false))))))))))))))))) vm)

/-- HOL `riscv$update_mstatus` (`update_mstatus_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "update_mstatus_def"]
def update_mstatus (arg0 : (mstatus × mstatus)) : mstatus :=
  match arg0 with
  | (orig, v) =>
  (let s0 : mstatus := (let r := ((let r := ((let r := ((let r := ((let r := ((let r := ((let r := ((let r := orig; { r with MIE := ((fun (_eta1 : Bool) => v.MIE)) r.MIE })); { r with MPRV := ((fun (_eta1 : (BitVec 2)) => v.MPRV)) r.MPRV })); { r with MIE1 := ((fun (_eta1 : Bool) => v.MIE1)) r.MIE1 })); { r with MPRV1 := ((fun (_eta1 : (BitVec 2)) => v.MPRV1)) r.MPRV1 })); { r with MIE2 := ((fun (_eta1 : Bool) => v.MIE2)) r.MIE2 })); { r with MPRV2 := ((fun (_eta1 : (BitVec 2)) => v.MPRV2)) r.MPRV2 })); { r with MIE3 := ((fun (_eta1 : Bool) => v.MIE3)) r.MIE3 })); { r with MPRV3 := ((fun (_eta1 : (BitVec 2)) => v.MPRV3)) r.MPRV3 }); (let r := ((let r := ((let r := ((let r := ((if (isValidVM v.VM) then ((let r := s0; { r with VM := ((fun (_eta1 : (BitVec 5)) => v.VM)) r.VM })) else s0)); { r with MMPRV := ((fun (_eta1 : Bool) => v.MMPRV)) r.MMPRV })); { r with MFS := ((fun (_eta1 : (BitVec 2)) => v.MFS)) r.MFS })); { r with MXS := ((fun (_eta1 : (BitVec 2)) => v.MXS)) r.MXS })); { r with MSD := ((fun (_eta1 : Bool) => (((((extStatus v.MXS) == ExtStatus.Dirty)) || (((extStatus v.MFS) == ExtStatus.Dirty)))))) r.MSD }))

/-- HOL `riscv$lower_sip_mip` (`lower_sip_mip_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lower_sip_mip_def"]
def lower_sip_mip (arg0 : (sip × mip)) : mip :=
  match arg0 with
  | (sip, mip) =>
  (let r := ((let r := mip; { r with STIP := ((fun (_eta1 : Bool) => sip.STIP)) r.STIP })); { r with SSIP := ((fun (_eta1 : Bool) => sip.SSIP)) r.SSIP })

/-- HOL `riscv$lower_sie_mie` (`lower_sie_mie_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lower_sie_mie_def"]
def lower_sie_mie (arg0 : (sie × mie)) : mie :=
  match arg0 with
  | (sie, mie) =>
  (let r := ((let r := mie; { r with STIE := ((fun (_eta1 : Bool) => sie.STIE)) r.STIE })); { r with SSIE := ((fun (_eta1 : Bool) => sie.SSIE)) r.SSIE })

/-- HOL `riscv$lower_sstatus_mstatus` (`lower_sstatus_mstatus_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "lower_sstatus_mstatus_def"]
def lower_sstatus_mstatus (arg0 : (sstatus × mstatus)) : mstatus :=
  match arg0 with
  | (sst, mst) =>
  (update_mstatus ((mst, ((let r := ((let r := ((let r := ((let r := ((let r := ((let r := ((«rec'mstatus» («reg'mstatus» mst))); { r with MMPRV := ((fun (_eta1 : Bool) => sst.SMPRV)) r.MMPRV })); { r with MXS := ((fun (_eta1 : (BitVec 2)) => sst.SXS)) r.MXS })); { r with MFS := ((fun (_eta1 : (BitVec 2)) => sst.SFS)) r.MFS })); { r with MPRV1 := ((fun (_eta1 : (BitVec 2)) => ((privLevel (if sst.SPS then Privilege.Supervisor else Privilege.User))))) r.MPRV1 })); { r with MIE1 := ((fun (_eta1 : Bool) => sst.SPIE)) r.MIE1 })); { r with MIE := ((fun (_eta1 : Bool) => sst.SIE)) r.MIE })))))

/-- HOL `riscv$rec'FPCSR` (`rec'FPCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'FPCSR_def"]
def «rec'FPCSR» (x : (BitVec 32)) : FPCSR :=
  (FPCSR.mk (x.getLsbD 3) (holWordExtract 3 7 5 x) (x.getLsbD 4) (x.getLsbD 0) (x.getLsbD 2) (x.getLsbD 1) (holWordExtract 24 31 8 x))

/-- HOL `riscv$write'reg'FPCSR` (`write'reg'FPCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'reg'FPCSR_def"]
def «write'reg'FPCSR» (arg0 : (FPCSR × (BitVec 32))) : FPCSR :=
  match arg0 with
  | (_u_, x) =>
  («rec'FPCSR» x)

/-- HOL `riscv$ext_status` (`ext_status_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "ext_status_def"]
def ext_status (e : ExtStatus) : (BitVec 2) :=
  (match e with | .Off => (BitVec.ofNat 2 0) | .Initial => (BitVec.ofNat 2 1) | .Clean => (BitVec.ofNat 2 2) | .Dirty => (BitVec.ofNat 2 3))

/-- HOL `riscv$write'CSRMap` (`write'CSRMap_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'CSRMap_def"]
def «write'CSRMap» (arg0 : ((BitVec 64) × (BitVec 12))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, csr) =>
  (fun (state : riscv_state) => (((fun (v1 : (BitVec 12)) => (if ((v1 == (BitVec.ofNat 12 1))) then ((let s : riscv_state := (let v : UserCSR := (state.c_UCSR state.procID); (let x1 : FPCSR := v.fpcsr; (let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := v; { r with fpcsr := ((fun (_eta1 : FPCSR) => ((«write'reg'FPCSR» ((x1, ((holBitFieldInsert 4 0 (holWordExtract 5 4 0 value) («reg'FPCSR» x1))))))))) r.fpcsr })) state.c_UCSR)))) r.c_UCSR }))); (let s_1 : riscv_state := (let v : MachineCSR := (s.c_MCSR s.procID); (let r := s; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s.procID ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MFS := ((fun (_eta1 : (BitVec 2)) => (ext_status ExtStatus.Dirty))) r.MFS })))) r.mstatus })) s.c_MCSR)))) r.c_MCSR })); (let v : MachineCSR := (s_1.c_MCSR s_1.procID); (let r := s_1; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s_1.procID ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MSD := ((fun (_eta1 : Bool) => true)) r.MSD })))) r.mstatus })) s_1.c_MCSR)))) r.c_MCSR }))))) else ((if ((v1 == (BitVec.ofNat 12 2))) then ((let s : riscv_state := (let v : UserCSR := (state.c_UCSR state.procID); (let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := v; { r with fpcsr := ((fun (_eta1 : FPCSR) => ((let r := v.fpcsr; { r with FRM := ((fun (_eta1 : (BitVec 3)) => (holWordExtract 3 2 0 value))) r.FRM })))) r.fpcsr })) state.c_UCSR)))) r.c_UCSR })); (let s_1 : riscv_state := (let v : MachineCSR := (s.c_MCSR s.procID); (let r := s; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s.procID ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MFS := ((fun (_eta1 : (BitVec 2)) => (ext_status ExtStatus.Dirty))) r.MFS })))) r.mstatus })) s.c_MCSR)))) r.c_MCSR })); (let v : MachineCSR := (s_1.c_MCSR s_1.procID); (let r := s_1; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s_1.procID ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MSD := ((fun (_eta1 : Bool) => true)) r.MSD })))) r.mstatus })) s_1.c_MCSR)))) r.c_MCSR }))))) else ((if ((v1 == (BitVec.ofNat 12 3))) then ((let s : riscv_state := (let v : UserCSR := (state.c_UCSR state.procID); (let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := v; { r with fpcsr := ((fun (_eta1 : FPCSR) => ((«write'reg'FPCSR» ((v.fpcsr, (holWordExtract 32 31 0 value))))))) r.fpcsr })) state.c_UCSR)))) r.c_UCSR })); (let s_1 : riscv_state := (let v : MachineCSR := (s.c_MCSR s.procID); (let r := s; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s.procID ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MFS := ((fun (_eta1 : (BitVec 2)) => (ext_status ExtStatus.Dirty))) r.MFS })))) r.mstatus })) s.c_MCSR)))) r.c_MCSR })); (let v : MachineCSR := (s_1.c_MCSR s_1.procID); (let r := s_1; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s_1.procID ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MSD := ((fun (_eta1 : Bool) => true)) r.MSD })))) r.mstatus })) s_1.c_MCSR)))) r.c_MCSR }))))) else ((if ((v1 == (BitVec.ofNat 12 256))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mstatus := ((fun (_eta1 : mstatus) => ((lower_sstatus_mstatus (((«rec'sstatus» value), ((state.c_MCSR state.procID).mstatus))))))) r.mstatus })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 257))) then ((let r := state; { r with c_SCSR := ((fun (_eta1 : ((BitVec 8) → SupervisorCSR)) => ((holUpdate state.procID ((let r := (state.c_SCSR state.procID); { r with stvec := ((fun (_eta1 : (BitVec 64)) => value)) r.stvec })) state.c_SCSR)))) r.c_SCSR })) else ((if ((v1 == (BitVec.ofNat 12 260))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mie := ((fun (_eta1 : mie) => ((lower_sie_mie (((«rec'sie» value), ((state.c_MCSR state.procID).mie))))))) r.mie })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 289))) then ((let s : riscv_state := (let r := state; { r with c_SCSR := ((fun (_eta1 : ((BitVec 8) → SupervisorCSR)) => ((holUpdate state.procID ((let r := (state.c_SCSR state.procID); { r with stimecmp := ((fun (_eta1 : (BitVec 64)) => value)) r.stimecmp })) state.c_SCSR)))) r.c_SCSR }); (let v : MachineCSR := (s.c_MCSR s.procID); (let r := s; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s.procID ((let r := v; { r with mip := ((fun (_eta1 : mip) => ((let r := v.mip; { r with STIP := ((fun (_eta1 : Bool) => false)) r.STIP })))) r.mip })) s.c_MCSR)))) r.c_MCSR })))) else ((if ((v1 == (BitVec.ofNat 12 320))) then ((let r := state; { r with c_SCSR := ((fun (_eta1 : ((BitVec 8) → SupervisorCSR)) => ((holUpdate state.procID ((let r := (state.c_SCSR state.procID); { r with sscratch := ((fun (_eta1 : (BitVec 64)) => value)) r.sscratch })) state.c_SCSR)))) r.c_SCSR })) else ((if ((v1 == (BitVec.ofNat 12 321))) then ((let r := state; { r with c_SCSR := ((fun (_eta1 : ((BitVec 8) → SupervisorCSR)) => ((holUpdate state.procID ((let r := (state.c_SCSR state.procID); { r with sepc := ((fun (_eta1 : (BitVec 64)) => ((value &&& ((BitVec.signExtend 64 (BitVec.ofNat 3 4))))))) r.sepc })) state.c_SCSR)))) r.c_SCSR })) else ((if ((v1 == (BitVec.ofNat 12 324))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mip := ((fun (_eta1 : mip) => ((lower_sip_mip (((«rec'sip» value), ((state.c_MCSR state.procID).mip))))))) r.mip })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 384))) then ((let r := state; { r with c_SCSR := ((fun (_eta1 : ((BitVec 8) → SupervisorCSR)) => ((holUpdate state.procID ((let r := (state.c_SCSR state.procID); { r with sptbr := ((fun (_eta1 : (BitVec 64)) => value)) r.sptbr })) state.c_SCSR)))) r.c_SCSR })) else ((if ((v1 == (BitVec.ofNat 12 385))) then ((let r := state; { r with c_SCSR := ((fun (_eta1 : ((BitVec 8) → SupervisorCSR)) => ((holUpdate state.procID ((let r := (state.c_SCSR state.procID); { r with sasid := ((fun (_eta1 : (BitVec 64)) => value)) r.sasid })) state.c_SCSR)))) r.c_SCSR })) else ((if ((v1 == (BitVec.ofNat 12 2304))) then ((let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := (state.c_UCSR state.procID); { r with cycle_delta := ((fun (_eta1 : (BitVec 64)) => ((value - (state.c_cycles state.procID))))) r.cycle_delta })) state.c_UCSR)))) r.c_UCSR })) else ((if ((v1 == (BitVec.ofNat 12 2305))) then ((let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := (state.c_UCSR state.procID); { r with time_delta := ((fun (_eta1 : (BitVec 64)) => (value - state.clock))) r.time_delta })) state.c_UCSR)))) r.c_UCSR })) else ((if ((v1 == (BitVec.ofNat 12 2306))) then ((let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := (state.c_UCSR state.procID); { r with instret_delta := ((fun (_eta1 : (BitVec 64)) => ((value - (state.c_instret state.procID))))) r.instret_delta })) state.c_UCSR)))) r.c_UCSR })) else ((if ((v1 == (BitVec.ofNat 12 2432))) then ((let v : UserCSR := (state.c_UCSR state.procID); (let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := v; { r with cycle_delta := ((fun (_eta1 : (BitVec 64)) => ((holBitFieldInsert 63 32 (((((holWordExtract 32 31 0 value) - ((holWordExtract 32 63 32 (state.c_cycles state.procID))))) <<< 32)) v.cycle_delta)))) r.cycle_delta })) state.c_UCSR)))) r.c_UCSR }))) else ((if ((v1 == (BitVec.ofNat 12 2433))) then ((let v : UserCSR := (state.c_UCSR state.procID); (let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := v; { r with time_delta := ((fun (_eta1 : (BitVec 64)) => ((holBitFieldInsert 63 32 (((((holWordExtract 32 31 0 value) - (holWordExtract 32 63 32 state.clock))) <<< 32)) v.time_delta)))) r.time_delta })) state.c_UCSR)))) r.c_UCSR }))) else ((if ((v1 == (BitVec.ofNat 12 2434))) then ((let v : UserCSR := (state.c_UCSR state.procID); (let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := v; { r with instret_delta := ((fun (_eta1 : (BitVec 64)) => ((holBitFieldInsert 63 32 (((((holWordExtract 32 31 0 value) - ((holWordExtract 32 63 32 (state.c_instret state.procID))))) <<< 32)) v.instret_delta)))) r.instret_delta })) state.c_UCSR)))) r.c_UCSR }))) else ((if ((v1 == (BitVec.ofNat 12 768))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mstatus := ((fun (_eta1 : mstatus) => ((update_mstatus ((((state.c_MCSR state.procID).mstatus), («rec'mstatus» value))))))) r.mstatus })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 769))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mtvec := ((fun (_eta1 : (BitVec 64)) => value)) r.mtvec })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 770))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mtdeleg := ((fun (_eta1 : mtdeleg) => («rec'mtdeleg» value))) r.mtdeleg })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 772))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mie := ((fun (_eta1 : mie) => («rec'mie» value))) r.mie })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 801))) then ((let s : riscv_state := (let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mtimecmp := ((fun (_eta1 : (BitVec 64)) => value)) r.mtimecmp })) state.c_MCSR)))) r.c_MCSR }); (let v : MachineCSR := (s.c_MCSR s.procID); (let r := s; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s.procID ((let r := v; { r with mip := ((fun (_eta1 : mip) => ((let r := v.mip; { r with MTIP := ((fun (_eta1 : Bool) => false)) r.MTIP })))) r.mip })) s.c_MCSR)))) r.c_MCSR })))) else ((if ((v1 == (BitVec.ofNat 12 1793))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mtime_delta := ((fun (_eta1 : (BitVec 64)) => (value - state.clock))) r.mtime_delta })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 1857))) then ((let v : MachineCSR := (state.c_MCSR state.procID); (let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := v; { r with mtime_delta := ((fun (_eta1 : (BitVec 64)) => ((holBitFieldInsert 63 32 (((((holWordExtract 32 31 0 value) - (holWordExtract 32 63 32 state.clock))) <<< 32)) v.mtime_delta)))) r.mtime_delta })) state.c_MCSR)))) r.c_MCSR }))) else ((if ((v1 == (BitVec.ofNat 12 832))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mscratch := ((fun (_eta1 : (BitVec 64)) => value)) r.mscratch })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 833))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mepc := ((fun (_eta1 : (BitVec 64)) => ((value &&& ((BitVec.signExtend 64 (BitVec.ofNat 3 4))))))) r.mepc })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 834))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mcause := ((fun (_eta1 : mcause) => («rec'mcause» value))) r.mcause })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 835))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mbadaddr := ((fun (_eta1 : (BitVec 64)) => value)) r.mbadaddr })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 836))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mip := ((fun (_eta1 : mip) => («rec'mip» value))) r.mip })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 896))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mbase := ((fun (_eta1 : (BitVec 64)) => value)) r.mbase })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 897))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mbound := ((fun (_eta1 : (BitVec 64)) => value)) r.mbound })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 898))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mibase := ((fun (_eta1 : (BitVec 64)) => value)) r.mibase })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 899))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mibound := ((fun (_eta1 : (BitVec 64)) => value)) r.mibound })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 900))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mdbase := ((fun (_eta1 : (BitVec 64)) => value)) r.mdbase })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 901))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mdbound := ((fun (_eta1 : (BitVec 64)) => value)) r.mdbound })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 2817))) then ((let r := state; { r with c_HCSR := ((fun (_eta1 : ((BitVec 8) → HypervisorCSR)) => ((holUpdate state.procID ((let r := (state.c_HCSR state.procID); { r with htime_delta := ((fun (_eta1 : (BitVec 64)) => (value - state.clock))) r.htime_delta })) state.c_HCSR)))) r.c_HCSR })) else ((if ((v1 == (BitVec.ofNat 12 2945))) then ((let v : HypervisorCSR := (state.c_HCSR state.procID); (let r := state; { r with c_HCSR := ((fun (_eta1 : ((BitVec 8) → HypervisorCSR)) => ((holUpdate state.procID ((let r := v; { r with htime_delta := ((fun (_eta1 : (BitVec 64)) => ((holBitFieldInsert 63 32 (((((holWordExtract 32 31 0 value) - (holWordExtract 32 63 32 state.clock))) <<< 32)) v.htime_delta)))) r.htime_delta })) state.c_HCSR)))) r.c_HCSR }))) else ((if ((v1 == (BitVec.ofNat 12 1920))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mtohost := ((fun (_eta1 : (BitVec 64)) => value)) r.mtohost })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 1921))) then ((let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate state.procID ((let r := (state.c_MCSR state.procID); { r with mfromhost := ((fun (_eta1 : (BitVec 64)) => value)) r.mfromhost })) state.c_MCSR)))) r.c_MCSR })) else ((if ((v1 == (BitVec.ofNat 12 1923))) then (sendIPI value state) else ((((«raise'exception» (Ta := Unit)) ((exception.INTERNAL_ERROR (((((BitVec.ofNat 8 117) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 120) :: (((BitVec.ofNat 8 112) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 99) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 100) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 67) :: (((BitVec.ofNat 8 83) :: (((BitVec.ofNat 8 82) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 119) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 105) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 111) :: (((BitVec.ofNat 8 32) :: (([] : (List HolChar))))))))))))))))))))))))))))))))))))))))))))))))))) ++ (holWordToHexString csr))))) state)).2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) csr))

/-- HOL `riscv$write'CSR` (`write'CSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'CSR_def"]
def «write'CSR» (arg0 : ((BitVec 64) × (BitVec 12))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => («write'CSRMap» (value, n) state))

/-- HOL `riscv$Delta` (`Delta_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Delta_def"]
def Delta (state : riscv_state) : StateDelta :=
  (state.c_update state.procID)

/-- HOL `riscv$write'Delta` (`write'Delta_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'Delta_def"]
def «write'Delta» (value : StateDelta) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_update := ((fun (_eta1 : ((BitVec 8) → StateDelta)) => (holUpdate state.procID value state.c_update))) r.c_update }))

/-- HOL `riscv$writeCSR` (`writeCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "writeCSR_def"]
def writeCSR (arg0 : ((BitVec 12) × (BitVec 64))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (csr, val) =>
  (fun (state : riscv_state) => (match (let s : riscv_state := («write'CSR» (val, csr) state); ((Delta s), s)) with | (v, s) => (match (let s0 : riscv_state := («write'Delta» ((let r := v; { r with addr := ((fun (_eta1 : (Option (BitVec 64))) => ((some (BitVec.setWidth 64 csr))))) r.addr })) s); ((Delta s0), s0)) with | (v_1, s_1) => (match (CSR csr s_1) with | (v0, s) => («write'Delta» ((let r := v_1; { r with data2 := ((fun (_eta1 : (Option (BitVec 64))) => (some v0))) r.data2 })) s)))))

/-- HOL `riscv$write'gpr` (`write'gpr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'gpr_def"]
def «write'gpr» (arg0 : ((BitVec 64) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => (let r := state; { r with c_gpr := ((fun (_eta1 : ((BitVec 8) → ((BitVec 5) → (BitVec 64)))) => ((holUpdate state.procID ((holUpdate n value (state.c_gpr state.procID))) state.c_gpr)))) r.c_gpr }))

/-- HOL `riscv$write'GPR` (`write'GPR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'GPR_def"]
def «write'GPR» (arg0 : ((BitVec 64) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => (if ((!((n == (BitVec.ofNat 5 0))))) then ((«write'gpr» (value, n) state)) else state))

/-- HOL `riscv$dfn'CSRRWI` (`dfn'CSRRWI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRWI_def"]
def «dfn'CSRRWI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (zimm, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, ((zimm, ((if ((zimm == (BitVec.ofNat 5 0))) then accessType.Read else accessType.Write)))))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((if ((!((zimm == (BitVec.ofNat 5 0))))) then ((writeCSR ((csr, (BitVec.setWidth 64 zimm))) s_1)) else s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

/-- HOL `riscv$dfn'CSRRW` (`dfn'CSRRW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRW_def"]
def «dfn'CSRRW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, (rs1, accessType.Write))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((writeCSR ((csr, (GPR rs1 s_1))) s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

/-- HOL `riscv$dfn'CSRRSI` (`dfn'CSRRSI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRSI_def"]
def «dfn'CSRRSI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (zimm, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, ((zimm, ((if ((zimm == (BitVec.ofNat 5 0))) then accessType.Read else accessType.Write)))))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((if ((!((zimm == (BitVec.ofNat 5 0))))) then ((writeCSR ((csr, ((v_1 ||| (BitVec.setWidth 64 zimm))))) s_1)) else s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

/-- HOL `riscv$dfn'CSRRS` (`dfn'CSRRS_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRS_def"]
def «dfn'CSRRS» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, ((rs1, ((if ((rs1 == (BitVec.ofNat 5 0))) then accessType.Read else accessType.Write)))))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((if ((!((rs1 == (BitVec.ofNat 5 0))))) then ((writeCSR ((csr, ((v_1 ||| (GPR rs1 s_1))))) s_1)) else s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

/-- HOL `riscv$dfn'CSRRCI` (`dfn'CSRRCI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRCI_def"]
def «dfn'CSRRCI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (zimm, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, ((zimm, ((if ((zimm == (BitVec.ofNat 5 0))) then accessType.Read else accessType.Write)))))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((if ((!((zimm == (BitVec.ofNat 5 0))))) then ((writeCSR ((csr, ((v_1 &&& ((~~~(BitVec.setWidth 64 zimm))))))) s_1)) else s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

/-- HOL `riscv$dfn'CSRRC` (`dfn'CSRRC_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRC_def"]
def «dfn'CSRRC» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, ((rs1, ((if ((rs1 == (BitVec.ofNat 5 0))) then accessType.Read else accessType.Write)))))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((if ((!((rs1 == (BitVec.ofNat 5 0))))) then ((writeCSR ((csr, ((v_1 &&& ((~~~(GPR rs1 s_1))))))) s_1)) else s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

/-- HOL `riscv$signalAddressException` (`signalAddressException_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "signalAddressException_def"]
def signalAddressException (arg0 : (ExceptionType × (BitVec 64))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (e, vAddr) =>
  (fun (state : riscv_state) => (setTrap ((e, (some vAddr))) state))

/-- HOL `riscv$dfn'SW` (`dfn'SW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SW_def"]
def «dfn'SW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s), 4)))) s)))))

/-- HOL `riscv$dfn'SH` (`dfn'SH_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SH_def"]
def «dfn'SH» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s), 2)))) s)))))

/-- HOL `riscv$dfn'SD` (`dfn'SD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SD_def"]
def «dfn'SD» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 64) := ((GPR rs1 s) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v_1, (fetchType.Data, accessType.Write))) s) with | (v0, s_1) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v_1) s_1) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s_1), 8)))) s_1))))))))

/-- HOL `riscv$dfn'SB` (`dfn'SB_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SB_def"]
def «dfn'SB» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s), 1)))) s)))))

/-- HOL `riscv$dfn'SRLW` (`dfn'SRLW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SRLW_def"]
def «dfn'SRLW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) >>> ((BitVec.setWidth 32 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)))), rd)) s)))))

/-- HOL `riscv$dfn'SRLIW` (`dfn'SRLIW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SRLIW_def"]
def «dfn'SRLIW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) >>> imm.toNat)))), rd)) s)))))

/-- HOL `riscv$dfn'SRLI` (`dfn'SRLI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SRLI_def"]
def «dfn'SRLI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 6)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if ((v && (imm.getLsbD 5))) then (signalException ExceptionType.Illegal_Instr s) else ((match (in32BitMode () s) with | (v_1, s_1) => («write'GPR» ((((((if v_1 then ((BitVec.setWidth 64 ((holWordExtract 32 31 0 (GPR rs1 s_1))))) else (GPR rs1 s_1))) >>> imm.toNat)), rd)) s_1))))))

/-- HOL `riscv$dfn'SRL` (`dfn'SRL_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SRL_def"]
def «dfn'SRL» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then ((«write'GPR» ((((BitVec.setWidth 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) >>> ((BitVec.setWidth 32 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)))), rd)) s)) else ((«write'GPR» (((((GPR rs1 s) >>> ((BitVec.setWidth 64 ((holWordExtract 6 5 0 (GPR rs2 s))))).toNat)), rd)) s)))))

/-- HOL `riscv$dfn'SRAW` (`dfn'SRAW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SRAW_def"]
def «dfn'SRAW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((BitVec.sshiftRight ((holWordExtract 32 31 0 (GPR rs1 s))) ((BitVec.setWidth 32 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)))), rd)) s)))))

/-- HOL `riscv$dfn'SRAIW` (`dfn'SRAIW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SRAIW_def"]
def «dfn'SRAIW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((BitVec.sshiftRight ((holWordExtract 32 31 0 (GPR rs1 s))) imm.toNat)))), rd)) s)))))

/-- HOL `riscv$dfn'SRAI` (`dfn'SRAI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SRAI_def"]
def «dfn'SRAI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 6)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if ((v && (imm.getLsbD 5))) then (signalException ExceptionType.Illegal_Instr s) else ((match (in32BitMode () s) with | (v_1, s_1) => («write'GPR» ((((BitVec.sshiftRight ((if v_1 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s_1))))) else (GPR rs1 s_1))) imm.toNat)), rd)) s_1))))))

/-- HOL `riscv$dfn'SRA` (`dfn'SRA_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SRA_def"]
def «dfn'SRA» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then ((«write'GPR» ((((BitVec.signExtend 64 ((BitVec.sshiftRight ((holWordExtract 32 31 0 (GPR rs1 s))) ((BitVec.setWidth 32 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)))), rd)) s)) else ((«write'GPR» ((((BitVec.sshiftRight (GPR rs1 s) ((BitVec.setWidth 64 ((holWordExtract 6 5 0 (GPR rs2 s))))).toNat)), rd)) s)))))

/-- HOL `riscv$dfn'SLLW` (`dfn'SLLW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SLLW_def"]
def «dfn'SLLW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) <<< ((BitVec.setWidth 32 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)))), rd)) s)))))

/-- HOL `riscv$dfn'SLLIW` (`dfn'SLLIW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SLLIW_def"]
def «dfn'SLLIW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) <<< imm.toNat)))), rd)) s)))))

/-- HOL `riscv$dfn'SLLI` (`dfn'SLLI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SLLI_def"]
def «dfn'SLLI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 6)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if ((v && (imm.getLsbD 5))) then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» (((((GPR rs1 s) <<< imm.toNat)), rd)) s)))))

/-- HOL `riscv$dfn'SLL` (`dfn'SLL_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SLL_def"]
def «dfn'SLL» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then ((«write'GPR» (((((GPR rs1 s) <<< ((BitVec.setWidth 64 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)), rd)) s)) else ((«write'GPR» (((((GPR rs1 s) <<< ((BitVec.setWidth 64 ((holWordExtract 6 5 0 (GPR rs2 s))))).toNat)), rd)) s)))))

/-- HOL `riscv$dfn'REMW` (`dfn'REMW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'REMW_def"]
def «dfn'REMW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs1 s)); (let v0 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs2 s)); (if ((v0 == (BitVec.ofNat 32 0))) then ((«write'GPR» (((BitVec.signExtend 64 v_1), rd)) s)) else ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.srem v_1 v0))), rd)) s)))))))))

/-- HOL `riscv$dfn'REMUW` (`dfn'REMUW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'REMUW_def"]
def «dfn'REMUW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs1 s)); (let v0 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs2 s)); (if ((v0 == (BitVec.ofNat 32 0))) then ((«write'GPR» (((BitVec.signExtend 64 v_1), rd)) s)) else ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.umod v_1 v0))), rd)) s)))))))))

/-- HOL `riscv$dfn'REMU` (`dfn'REMU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'REMU_def"]
def «dfn'REMU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (if (((GPR rs2 state) == (BitVec.ofNat 64 0))) then ((«write'GPR» (((GPR rs1 state), rd)) state)) else ((«write'GPR» ((((BitVec.umod (GPR rs1 state) (GPR rs2 state))), rd)) state))))

/-- HOL `riscv$dfn'REM` (`dfn'REM_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'REM_def"]
def «dfn'REM» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (if (((GPR rs2 state) == (BitVec.ofNat 64 0))) then ((«write'GPR» (((GPR rs1 state), rd)) state)) else ((«write'GPR» ((((BitVec.srem (GPR rs1 state) (GPR rs2 state))), rd)) state))))

/-- HOL `riscv$dfn'MULW` (`dfn'MULW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'MULW_def"]
def «dfn'MULW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 ((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) * ((holWordExtract 32 31 0 (GPR rs2 s))))))))))), rd)) s)))))

/-- HOL `riscv$dfn'MULHU` (`dfn'MULHU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'MULHU_def"]
def «dfn'MULHU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (let prod : (BitVec 128) := (((if v then ((BitVec.setWidth 128 ((holWordExtract 32 31 0 (GPR rs1 s))))) else ((BitVec.setWidth 128 (GPR rs1 s))))) * ((if v0 then ((BitVec.setWidth 128 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else ((BitVec.setWidth 128 (GPR rs2 s0)))))); (match (in32BitMode () s0) with | (v_1, s_1) => («write'GPR» ((((if v_1 then ((BitVec.setWidth 64 (holWordExtract 32 63 32 prod))) else (holWordExtract 64 127 64 prod))), rd)) s_1))))))

/-- HOL `riscv$dfn'MULHSU` (`dfn'MULHSU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'MULHSU_def"]
def «dfn'MULHSU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (let prod : (BitVec 128) := (((if v then ((BitVec.signExtend 128 ((holWordExtract 32 31 0 (GPR rs1 s))))) else ((BitVec.signExtend 128 (GPR rs1 s))))) * ((if v0 then ((BitVec.setWidth 128 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else ((BitVec.setWidth 128 (GPR rs2 s0)))))); (match (in32BitMode () s0) with | (v_1, s_1) => («write'GPR» ((((if v_1 then ((BitVec.signExtend 64 (holWordExtract 32 63 32 prod))) else (holWordExtract 64 127 64 prod))), rd)) s_1))))))

/-- HOL `riscv$dfn'MULH` (`dfn'MULH_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'MULH_def"]
def «dfn'MULH» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (let prod : (BitVec 128) := (((BitVec.signExtend 128 ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))))) * ((BitVec.signExtend 128 ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0)))))); (match (in32BitMode () s0) with | (v_1, s_1) => («write'GPR» ((((if v_1 then ((BitVec.signExtend 64 (holWordExtract 32 63 32 prod))) else ((BitVec.signExtend 64 (holWordExtract 64 127 64 prod))))), rd)) s_1))))))

/-- HOL `riscv$dfn'MUL` (`dfn'MUL_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'MUL_def"]
def «dfn'MUL» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) * (GPR rs2 state))), rd)) state))

/-- HOL `riscv$dfn'DIVW` (`dfn'DIVW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'DIVW_def"]
def «dfn'DIVW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v0 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs2 s)); (if ((v0 == (BitVec.ofNat 32 0))) then ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))), rd)) s)) else ((«write'GPR» ((((BitVec.signExtend 64 ((BitVec.sdiv ((holWordExtract 32 31 0 (GPR rs1 s))) v0)))), rd)) s))))))))

/-- HOL `riscv$dfn'DIVUW` (`dfn'DIVUW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'DIVUW_def"]
def «dfn'DIVUW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v0 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs2 s)); (if ((v0 == (BitVec.ofNat 32 0))) then ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))), rd)) s)) else ((«write'GPR» ((((BitVec.signExtend 64 ((BitVec.udiv ((holWordExtract 32 31 0 (GPR rs1 s))) v0)))), rd)) s))))))))

/-- HOL `riscv$dfn'DIVU` (`dfn'DIVU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'DIVU_def"]
def «dfn'DIVU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (let v0_1 : (BitVec 64) := (if v0 then ((BitVec.setWidth 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0)); (if ((v0_1 == (BitVec.ofNat 64 0))) then ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))), rd)) s0)) else ((«write'GPR» ((((BitVec.udiv ((if v then ((BitVec.setWidth 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) v0_1)), rd)) s0)))))))

/-- HOL `riscv$dfn'DIV` (`dfn'DIV_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'DIV_def"]
def «dfn'DIV» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (if (((GPR rs2 state) == (BitVec.ofNat 64 0))) then ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))), rd)) state)) else ((«write'GPR» ((((BitVec.sdiv (GPR rs1 state) (GPR rs2 state))), rd)) state))))

/-- HOL `riscv$dfn'LWU` (`dfn'LWU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LWU_def"]
def «dfn'LWU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 64) := ((GPR rs1 s) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v_1, (fetchType.Data, accessType.Read))) s) with | (v0, s_1) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v_1) s_1) | some pAddr => («write'GPR» ((((BitVec.setWidth 64 ((holWordExtract 32 31 0 (rawReadData pAddr s_1))))), rd)) s_1))))))))

/-- HOL `riscv$dfn'LW` (`dfn'LW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LW_def"]
def «dfn'LW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s))))), rd)) s)))))

/-- HOL `riscv$dfn'LHU` (`dfn'LHU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LHU_def"]
def «dfn'LHU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'GPR» ((((BitVec.setWidth 64 ((holWordExtract 16 15 0 (rawReadData pAddr s))))), rd)) s)))))

/-- HOL `riscv$dfn'LH` (`dfn'LH_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LH_def"]
def «dfn'LH» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 16 15 0 (rawReadData pAddr s))))), rd)) s)))))

/-- HOL `riscv$dfn'LD` (`dfn'LD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LD_def"]
def «dfn'LD» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 64) := ((GPR rs1 s) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v_1, (fetchType.Data, accessType.Read))) s) with | (v0, s_1) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v_1) s_1) | some pAddr => («write'GPR» (((rawReadData pAddr s_1), rd)) s_1))))))))

/-- HOL `riscv$dfn'LBU` (`dfn'LBU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LBU_def"]
def «dfn'LBU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'GPR» ((((BitVec.setWidth 64 ((holWordExtract 8 7 0 (rawReadData pAddr s))))), rd)) s)))))

/-- HOL `riscv$dfn'LB` (`dfn'LB_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LB_def"]
def «dfn'LB» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 8 7 0 (rawReadData pAddr s))))), rd)) s)))))

/-- HOL `riscv$dfn'FETCH_MISALIGNED` (`dfn'FETCH_MISALIGNED_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FETCH_MISALIGNED_def"]
def «dfn'FETCH_MISALIGNED» (addr : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (signalAddressException (ExceptionType.Fetch_Misaligned, addr) state))

/-- HOL `riscv$dfn'FETCH_FAULT` (`dfn'FETCH_FAULT_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FETCH_FAULT_def"]
def «dfn'FETCH_FAULT» (addr : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (signalAddressException (ExceptionType.Fetch_Fault, addr) state))

/-- HOL `riscv$fpr` (`fpr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "fpr_def"]
def fpr (n : (BitVec 5)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (state.c_fpr state.procID n))

/-- HOL `riscv$FPRS` (`FPRS_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FPRS_def"]
def FPRS (n : (BitVec 5)) : (riscv_state → (BitVec 32)) :=
  (fun (state : riscv_state) => (holWordExtract 32 31 0 (fpr n state)))

/-- HOL `riscv$dfn'FSW` (`dfn'FSW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSW_def"]
def «dfn'FSW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, ((((BitVec.setWidth 64 (FPRS rs2 s))), 4)))) s)))))

/-- HOL `riscv$FPRD` (`FPRD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FPRD_def"]
def FPRD (n : (BitVec 5)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (fpr n state))

/-- HOL `riscv$dfn'FSD` (`dfn'FSD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSD_def"]
def «dfn'FSD» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((FPRD rs2 s), 8)))) s)))))

/-- HOL `riscv$write'fpr` (`write'fpr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'fpr_def"]
def «write'fpr» (arg0 : ((BitVec 64) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => (let r := state; { r with c_fpr := ((fun (_eta1 : ((BitVec 8) → ((BitVec 5) → (BitVec 64)))) => ((holUpdate state.procID ((holUpdate n value (state.c_fpr state.procID))) state.c_fpr)))) r.c_fpr }))

/-- HOL `riscv$write'FPRS` (`write'FPRS_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'FPRS_def"]
def «write'FPRS» (arg0 : ((BitVec 32) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => («write'fpr» ((((holBitFieldInsert 31 0 value (fpr n state))), n)) state))

/-- HOL `riscv$dfn'FLW` (`dfn'FLW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLW_def"]
def «dfn'FLW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'FPRS» ((((holWordExtract 32 31 0 (rawReadData pAddr s))), rd)) s)))))

/-- HOL `riscv$write'FPRD` (`write'FPRD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'FPRD_def"]
def «write'FPRD» (arg0 : ((BitVec 64) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => («write'fpr» (value, n) state))

/-- HOL `riscv$dfn'FLD` (`dfn'FLD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLD_def"]
def «dfn'FLD» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'FPRD» (((rawReadData pAddr s), rd)) s)))))

/-- HOL `riscv$FP32_Sign` (`FP32_Sign_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FP32_Sign_def"]
def FP32_Sign (x : (BitVec 32)) : Bool :=
  (x.getLsbD 31)

/-- HOL `riscv$writeFPRS` (`writeFPRS_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "writeFPRS_def"]
def writeFPRS (arg0 : ((BitVec 5) × (BitVec 32))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, val) =>
  (fun (state : riscv_state) => (match (let s : riscv_state := («write'FPRS» (val, rd) state); ((MCSR s), s)) with | (v, s) => (match (let s0 : riscv_state := («write'MCSR» ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MFS := ((fun (_eta1 : (BitVec 2)) => (ext_status ExtStatus.Dirty))) r.MFS })))) r.mstatus })) s); ((MCSR s0), s0)) with | (v_1, s_1) => (match (let s0 : riscv_state := («write'MCSR» ((let r := v_1; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v_1.mstatus; { r with MSD := ((fun (_eta1 : Bool) => true)) r.MSD })))) r.mstatus })) s_1); ((Delta s0), s0)) with | (v, s) => («write'Delta» ((let r := v; { r with data1 := ((fun (_eta1 : (Option (BitVec 64))) => ((some (BitVec.setWidth 64 val))))) r.data1 })) s)))))

/-- HOL `riscv$dfn'FSGNJ_S` (`dfn'FSGNJ_S_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJ_S_def"]
def «dfn'FSGNJ_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (writeFPRS ((rd, ((BitVec.setWidth 32 (((holV2w 1 ((((FP32_Sign (FPRS rs2 state))) :: (([] : (List Bool))))))) ++ ((holWordExtract 31 30 0 (FPRS rs1 state)))))))) state))

/-- HOL `riscv$FP64_Sign` (`FP64_Sign_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FP64_Sign_def"]
def FP64_Sign (x : (BitVec 64)) : Bool :=
  (x.getLsbD 63)

/-- HOL `riscv$writeFPRD` (`writeFPRD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "writeFPRD_def"]
def writeFPRD (arg0 : ((BitVec 5) × (BitVec 64))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, val) =>
  (fun (state : riscv_state) => (match (let s : riscv_state := («write'FPRD» (val, rd) state); ((MCSR s), s)) with | (v, s) => (match (let s0 : riscv_state := («write'MCSR» ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MFS := ((fun (_eta1 : (BitVec 2)) => (ext_status ExtStatus.Dirty))) r.MFS })))) r.mstatus })) s); ((MCSR s0), s0)) with | (v_1, s_1) => (match (let s0 : riscv_state := («write'MCSR» ((let r := v_1; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v_1.mstatus; { r with MSD := ((fun (_eta1 : Bool) => true)) r.MSD })))) r.mstatus })) s_1); ((Delta s0), s0)) with | (v, s) => («write'Delta» ((let r := v; { r with data1 := ((fun (_eta1 : (Option (BitVec 64))) => (some val))) r.data1 })) s)))))

/-- HOL `riscv$dfn'FSGNJ_D` (`dfn'FSGNJ_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJ_D_def"]
def «dfn'FSGNJ_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (writeFPRD ((rd, ((BitVec.setWidth 64 (((holV2w 1 ((((FP64_Sign (FPRD rs2 state))) :: (([] : (List Bool))))))) ++ ((holWordExtract 63 62 0 (FPRD rs1 state)))))))) state))

/-- HOL `riscv$dfn'FSGNJX_S` (`dfn'FSGNJX_S_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJX_S_def"]
def «dfn'FSGNJX_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (writeFPRS ((rd, ((BitVec.setWidth 32 (((((holV2w 1 ((((FP32_Sign (FPRS rs2 state))) :: (([] : (List Bool))))))) ^^^ ((holV2w 1 (((FP32_Sign v) :: (([] : (List Bool))))))))) ++ (holWordExtract 31 30 0 v)))))) state)))

/-- HOL `riscv$dfn'FSGNJX_D` (`dfn'FSGNJX_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJX_D_def"]
def «dfn'FSGNJX_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (writeFPRD ((rd, ((BitVec.setWidth 64 (((((holV2w 1 ((((FP64_Sign (FPRD rs2 state))) :: (([] : (List Bool))))))) ^^^ ((holV2w 1 (((FP64_Sign v) :: (([] : (List Bool))))))))) ++ (holWordExtract 63 62 0 v)))))) state)))

/-- HOL `riscv$dfn'FSGNJN_S` (`dfn'FSGNJN_S_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJN_S_def"]
def «dfn'FSGNJN_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (writeFPRS ((rd, ((BitVec.setWidth 32 (((holV2w 1 ((((!((FP32_Sign (FPRS rs2 state))))) :: (([] : (List Bool))))))) ++ ((holWordExtract 31 30 0 (FPRS rs1 state)))))))) state))

/-- HOL `riscv$dfn'FSGNJN_D` (`dfn'FSGNJN_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJN_D_def"]
def «dfn'FSGNJN_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (writeFPRD ((rd, ((BitVec.setWidth 64 (((holV2w 1 ((((!((FP64_Sign (FPRD rs2 state))))) :: (([] : (List Bool))))))) ++ ((holWordExtract 63 62 0 (FPRD rs1 state)))))))) state))

/-- HOL `riscv$dfn'FMV_X_S` (`dfn'FMV_X_S_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMV_X_S_def"]
def «dfn'FMV_X_S» (arg0 : ((BitVec 5) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, rs) =>
  (fun (state : riscv_state) => («write'GPR» ((((BitVec.signExtend 64 (FPRS rs state))), rd)) state))

/-- HOL `riscv$dfn'FMV_X_D` (`dfn'FMV_X_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMV_X_D_def"]
def «dfn'FMV_X_D» (arg0 : ((BitVec 5) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, rs) =>
  (fun (state : riscv_state) => («write'GPR» ((((BitVec.signExtend 64 (FPRD rs state))), rd)) state))

/-- HOL `riscv$dfn'FMV_S_X` (`dfn'FMV_S_X_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMV_S_X_def"]
def «dfn'FMV_S_X» (arg0 : ((BitVec 5) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, rs) =>
  (fun (state : riscv_state) => (writeFPRS ((rd, ((holWordExtract 32 31 0 (GPR rs state))))) state))

/-- HOL `riscv$dfn'FMV_D_X` (`dfn'FMV_D_X_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMV_D_X_def"]
def «dfn'FMV_D_X» (arg0 : ((BitVec 5) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, rs) =>
  (fun (state : riscv_state) => (writeFPRD ((rd, (GPR rs state))) state))

/-- HOL `riscv$l3round` (`l3round_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "l3round_def"]
def l3round (rnd : Rounding) : (Option HolRounding) :=
  (match rnd with | .RNE => (some HolRounding.roundTiesToEven) | .RTZ => (some HolRounding.roundTowardZero) | .RDN => (some HolRounding.roundTowardNegative) | .RUP => (some HolRounding.roundTowardPositive) | .RMM => (none : (Option HolRounding)) | .RDYN => (none : (Option HolRounding)))

/-- HOL `riscv$fcsr` (`fcsr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "fcsr_def"]
def fcsr (state : riscv_state) : FPCSR :=
  (state.c_UCSR state.procID).fpcsr

/-- HOL `riscv$rnd_mode_dynamic` (`rnd_mode_dynamic_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rnd_mode_dynamic_def"]
def rnd_mode_dynamic (rnd : (BitVec 3)) : (Option Rounding) :=
  (((fun (v : (BitVec 3)) => (if ((v == (BitVec.ofNat 3 0))) then (some Rounding.RNE) else ((if ((v == (BitVec.ofNat 3 1))) then (some Rounding.RTZ) else ((if ((v == (BitVec.ofNat 3 2))) then (some Rounding.RDN) else ((if ((v == (BitVec.ofNat 3 3))) then (some Rounding.RUP) else ((if ((v == (BitVec.ofNat 3 4))) then (some Rounding.RMM) else ((none : (Option Rounding)))))))))))))) rnd)

/-- HOL `riscv$rnd_mode_static` (`rnd_mode_static_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rnd_mode_static_def"]
def rnd_mode_static (rnd : (BitVec 3)) : (Option Rounding) :=
  (((fun (v : (BitVec 3)) => (if ((v == (BitVec.ofNat 3 0))) then (some Rounding.RNE) else ((if ((v == (BitVec.ofNat 3 1))) then (some Rounding.RTZ) else ((if ((v == (BitVec.ofNat 3 2))) then (some Rounding.RDN) else ((if ((v == (BitVec.ofNat 3 3))) then (some Rounding.RUP) else ((if ((v == (BitVec.ofNat 3 4))) then (some Rounding.RMM) else ((if ((v == (BitVec.ofNat 3 7))) then (some Rounding.RDYN) else ((none : (Option Rounding)))))))))))))))) rnd)

/-- HOL `riscv$round` (`round_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "round_def"]
def round (rnd : (BitVec 3)) : (riscv_state → (Option HolRounding)) :=
  (fun (state : riscv_state) => (match (rnd_mode_static rnd) with | none => (none : (Option HolRounding)) | some v => (match v with | .RNE => (l3round Rounding.RNE) | .RTZ => (l3round Rounding.RTZ) | .RDN => (l3round Rounding.RDN) | .RUP => (l3round Rounding.RUP) | .RMM => (l3round Rounding.RMM) | .RDYN => (match (rnd_mode_dynamic ((fcsr state).FRM)) with | none => (none : (Option HolRounding)) | some frm => (l3round frm)))))

/-- HOL `riscv$dfn'FCVT_W_S` (`dfn'FCVT_W_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_W_S_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_W_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 32) := (FPRS rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((v == (BitVec.ofNat 32 2139095040))))) then ((BitVec.ofNat 64 (((2 ^ 31) - 1)))) else ((if ((v == (BitVec.ofNat 32 4286578688))) then ((-((BitVec.ofNat 64 (2 ^ 31))))) else ((if ((decide (val > (((((Int.ofNat 2) ^ 31)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 31) - 1)))) else ((if ((decide (val < ((-(((Int.ofNat 2) ^ 31))))))) then ((-((BitVec.ofNat 64 (2 ^ 31))))) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_W_D` (`dfn'FCVT_W_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_W_D_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_W_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 64) := (FPRD rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((v == (BitVec.ofNat 64 9218868437227405312))))) then ((BitVec.ofNat 64 (((2 ^ 31) - 1)))) else ((if ((v == (BitVec.ofNat 64 18442240474082181120))) then ((-((BitVec.ofNat 64 (2 ^ 31))))) else ((if ((decide (val > (((((Int.ofNat 2) ^ 31)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 31) - 1)))) else ((if ((decide (val < ((-(((Int.ofNat 2) ^ 31))))))) then ((-((BitVec.ofNat 64 (2 ^ 31))))) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_WU_S` (`dfn'FCVT_WU_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_WU_S_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_WU_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 32) := (FPRS rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((v == (BitVec.ofNat 32 2139095040))))) then ((BitVec.ofNat 64 (((2 ^ 32) - 1)))) else ((if ((v == (BitVec.ofNat 32 4286578688))) then (BitVec.ofNat 64 0) else ((if ((decide (val > (((((Int.ofNat 2) ^ 32)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 32) - 1)))) else ((if ((decide (val < (Int.ofNat 0)))) then (BitVec.ofNat 64 0) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_WU_D` (`dfn'FCVT_WU_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_WU_D_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_WU_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 64) := (FPRD rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((v == (BitVec.ofNat 64 9218868437227405312))))) then ((BitVec.ofNat 64 (((2 ^ 32) - 1)))) else ((if ((v == (BitVec.ofNat 64 18442240474082181120))) then (BitVec.ofNat 64 0) else ((if ((decide (val > (((((Int.ofNat 2) ^ 32)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 32) - 1)))) else ((if ((decide (val < (Int.ofNat 0)))) then (BitVec.ofNat 64 0) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_L_S` (`dfn'FCVT_L_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_L_S_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_L_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 32) := (FPRS rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((v == (BitVec.ofNat 32 2139095040))))) then ((BitVec.ofNat 64 (((2 ^ 63) - 1)))) else ((if ((v == (BitVec.ofNat 32 4286578688))) then ((-((BitVec.ofNat 64 (2 ^ 63))))) else ((if ((decide (val > (((((Int.ofNat 2) ^ 63)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 63) - 1)))) else ((if ((decide (val < ((-(((Int.ofNat 2) ^ 63))))))) then ((-((BitVec.ofNat 64 (2 ^ 63))))) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_L_D` (`dfn'FCVT_L_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_L_D_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_L_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 64) := (FPRD rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((v == (BitVec.ofNat 64 9218868437227405312))))) then ((BitVec.ofNat 64 (((2 ^ 63) - 1)))) else ((if ((v == (BitVec.ofNat 64 18442240474082181120))) then ((-((BitVec.ofNat 64 (2 ^ 63))))) else ((if ((decide (val > (((((Int.ofNat 2) ^ 63)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 63) - 1)))) else ((if ((decide (val < ((-(((Int.ofNat 2) ^ 63))))))) then ((-((BitVec.ofNat 64 (2 ^ 63))))) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_LU_S` (`dfn'FCVT_LU_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_LU_S_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_LU_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 32) := (FPRS rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((v == (BitVec.ofNat 32 2139095040))))) then ((BitVec.ofNat 64 (((2 ^ 64) - 1)))) else ((if ((v == (BitVec.ofNat 32 4286578688))) then (BitVec.ofNat 64 0) else ((if ((decide (val > (((((Int.ofNat 2) ^ 64)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 64) - 1)))) else ((if ((decide (val < (Int.ofNat 0)))) then (BitVec.ofNat 64 0) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_LU_D` (`dfn'FCVT_LU_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_LU_D_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_LU_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 64) := (FPRD rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((v == (BitVec.ofNat 64 9218868437227405312))))) then ((BitVec.ofNat 64 (((2 ^ 64) - 1)))) else ((if ((v == (BitVec.ofNat 64 18442240474082181120))) then (BitVec.ofNat 64 0) else ((if ((decide (val > (((((Int.ofNat 2) ^ 64)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 64) - 1)))) else ((if ((decide (val < (Int.ofNat 0)))) then (BitVec.ofNat 64 0) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$FP32_IsSignalingNan` (`FP32_IsSignalingNan_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FP32_IsSignalingNan_def"]
def FP32_IsSignalingNan (x : (BitVec 32)) : Bool :=
  ((((holWordExtract 8 30 23 x) == (BitVec.ofNat 8 255))) && (((((x.getLsbD 22) == false)) && ((!(((holWordExtract 22 21 0 x) == (BitVec.ofNat 22 0))))))))

/-- HOL `riscv$RV32_CanonicalNan` (`RV32_CanonicalNan_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "RV32_CanonicalNan_def"]
def RV32_CanonicalNan  : (BitVec 32) :=
  (BitVec.ofNat 32 2143289344)

/-- HOL `riscv$FP64_IsSignalingNan` (`FP64_IsSignalingNan_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FP64_IsSignalingNan_def"]
def FP64_IsSignalingNan (x : (BitVec 64)) : Bool :=
  ((((holWordExtract 11 62 52 x) == (BitVec.ofNat 11 2047))) && (((((x.getLsbD 51) == false)) && ((!(((holWordExtract 51 50 0 x) == (BitVec.ofNat 51 0))))))))

/-- HOL `riscv$RV64_CanonicalNan` (`RV64_CanonicalNan_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "RV64_CanonicalNan_def"]
def RV64_CanonicalNan  : (BitVec 64) :=
  (BitVec.ofNat 64 9221120237041090560)

/-- HOL `riscv$dfn'FMIN_S` (`dfn'FMIN_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMIN_S_def" (reals_as_rational_cuts)]
def «dfn'FMIN_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (let v0 : (BitVec 32) := (FPRS rs2 state); (writeFPRS ((rd, ((match (holFloatCompare ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8) ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8)) with | .lt => v | .eq => v | .gt => v0 | .un => (if (((((FP32_IsSignalingNan v) || (FP32_IsSignalingNan v0))) || (((v == RV32_CanonicalNan) && (v0 == RV32_CanonicalNan))))) then RV32_CanonicalNan else ((if (v == RV32_CanonicalNan) then v0 else v))))))) state))))

/-- HOL `riscv$dfn'FMIN_D` (`dfn'FMIN_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMIN_D_def" (reals_as_rational_cuts)]
def «dfn'FMIN_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (let v0 : (BitVec 64) := (FPRD rs2 state); (writeFPRD ((rd, ((match (holFloatCompare ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11) ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11)) with | .lt => v | .eq => v | .gt => v0 | .un => (if (((((FP64_IsSignalingNan v) || (FP64_IsSignalingNan v0))) || (((v == RV64_CanonicalNan) && (v0 == RV64_CanonicalNan))))) then RV64_CanonicalNan else ((if (v == RV64_CanonicalNan) then v0 else v))))))) state))))

/-- HOL `riscv$dfn'FMAX_S` (`dfn'FMAX_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMAX_S_def" (reals_as_rational_cuts)]
def «dfn'FMAX_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (let v0 : (BitVec 32) := (FPRS rs2 state); (writeFPRS ((rd, ((match (holFloatCompare ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8) ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8)) with | .lt => v0 | .eq => v0 | .gt => v | .un => (if (((((FP32_IsSignalingNan v) || (FP32_IsSignalingNan v0))) || (((v == RV32_CanonicalNan) && (v0 == RV32_CanonicalNan))))) then RV32_CanonicalNan else ((if (v == RV32_CanonicalNan) then v0 else v))))))) state))))

/-- HOL `riscv$dfn'FMAX_D` (`dfn'FMAX_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMAX_D_def" (reals_as_rational_cuts)]
def «dfn'FMAX_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (let v0 : (BitVec 64) := (FPRD rs2 state); (writeFPRD ((rd, ((match (holFloatCompare ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11) ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11)) with | .lt => v0 | .eq => v0 | .gt => v | .un => (if (((((FP64_IsSignalingNan v) || (FP64_IsSignalingNan v0))) || (((v == RV64_CanonicalNan) && (v0 == RV64_CanonicalNan))))) then RV64_CanonicalNan else ((if (v == RV64_CanonicalNan) then v0 else v))))))) state))))

/-- HOL `riscv$write'fcsr` (`write'fcsr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'fcsr_def"]
def «write'fcsr» (value : FPCSR) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let s : riscv_state := (let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := (state.c_UCSR state.procID); { r with fpcsr := ((fun (_eta1 : FPCSR) => value)) r.fpcsr })) state.c_UCSR)))) r.c_UCSR }); (let s_1 : riscv_state := (let v : MachineCSR := (s.c_MCSR s.procID); (let r := s; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s.procID ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MFS := ((fun (_eta1 : (BitVec 2)) => (ext_status ExtStatus.Dirty))) r.MFS })))) r.mstatus })) s.c_MCSR)))) r.c_MCSR })); (let v : MachineCSR := (s_1.c_MCSR s_1.procID); (let r := s_1; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s_1.procID ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MSD := ((fun (_eta1 : Bool) => true)) r.MSD })))) r.mstatus })) s_1.c_MCSR)))) r.c_MCSR })))))

/-- HOL `riscv$setFP_Invalid` (`setFP_Invalid_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "setFP_Invalid_def"]
def setFP_Invalid (_u_ : Unit) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => («write'fcsr» ((let r := (fcsr state); { r with NV := ((fun (_eta1 : Bool) => true)) r.NV })) state))

/-- HOL `riscv$dfn'FLT_S` (`dfn'FLT_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLT_S_def" (reals_as_rational_cuts)]
def «dfn'FLT_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (let v0 : (BitVec 32) := (FPRS rs2 state); (if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((holFloatIsNan ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8))))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8) ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8)) with | .lt => (BitVec.ofNat 64 1) | .eq => (BitVec.ofNat 64 0) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$dfn'FLT_D` (`dfn'FLT_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLT_D_def" (reals_as_rational_cuts)]
def «dfn'FLT_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (let v0 : (BitVec 64) := (FPRD rs2 state); (if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((holFloatIsNan ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11))))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11) ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11)) with | .lt => (BitVec.ofNat 64 1) | .eq => (BitVec.ofNat 64 0) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$dfn'FLE_S` (`dfn'FLE_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLE_S_def" (reals_as_rational_cuts)]
def «dfn'FLE_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (let v0 : (BitVec 32) := (FPRS rs2 state); (if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((holFloatIsNan ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8))))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8) ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8)) with | .lt => (BitVec.ofNat 64 1) | .eq => (BitVec.ofNat 64 1) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$dfn'FLE_D` (`dfn'FLE_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLE_D_def" (reals_as_rational_cuts)]
def «dfn'FLE_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (let v0 : (BitVec 64) := (FPRD rs2 state); (if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((holFloatIsNan ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11))))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11) ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11)) with | .lt => (BitVec.ofNat 64 1) | .eq => (BitVec.ofNat 64 1) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$dfn'FEQ_S` (`dfn'FEQ_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FEQ_S_def" (reals_as_rational_cuts)]
def «dfn'FEQ_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (let v0 : (BitVec 32) := (FPRS rs2 state); (if (((FP32_IsSignalingNan v) || (FP32_IsSignalingNan v0))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8) ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8)) with | .lt => (BitVec.ofNat 64 0) | .eq => (BitVec.ofNat 64 1) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$dfn'FEQ_D` (`dfn'FEQ_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FEQ_D_def" (reals_as_rational_cuts)]
def «dfn'FEQ_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (let v0 : (BitVec 64) := (FPRD rs2 state); (if (((FP64_IsSignalingNan v) || (FP64_IsSignalingNan v0))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11) ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11)) with | .lt => (BitVec.ofNat 64 0) | .eq => (BitVec.ofNat 64 1) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$Skip` (`Skip_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Skip_def"]
def Skip (state : riscv_state) : (BitVec 64) :=
  (state.c_Skip state.procID)

/-- HOL `riscv$branchTo` (`branchTo_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "branchTo_def"]
def branchTo (newPC : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => («write'NextFetch» ((some (TransferControl.BranchTo newPC))) state))

/-- HOL `riscv$dfn'JALR` (`dfn'JALR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'JALR_def"]
def «dfn'JALR» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((((GPR rs1 state) + (BitVec.signExtend 64 imm))) &&& ((BitVec.signExtend 64 (BitVec.ofNat 2 2)))); (if (v.getLsbD 0) then ((signalAddressException (ExceptionType.Fetch_Misaligned, v) state)) else ((branchTo v ((«write'GPR» (((((PC state) + (Skip state))), rd)) state)))))))

/-- HOL `riscv$dfn'JAL` (`dfn'JAL_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'JAL_def"]
def «dfn'JAL» (arg0 : ((BitVec 5) × (BitVec 20))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, imm) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((PC state) + (((BitVec.signExtend 64 imm) <<< 1))); (if (v.getLsbD 0) then ((signalAddressException (ExceptionType.Fetch_Misaligned, v) state)) else ((branchTo v ((«write'GPR» (((((PC state) + (Skip state))), rd)) state)))))))

/-- HOL `riscv$dfn'BNE` (`dfn'BNE_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BNE_def"]
def «dfn'BNE» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((!((((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) == ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

/-- HOL `riscv$dfn'BLTU` (`dfn'BLTU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BLTU_def"]
def «dfn'BLTU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((BitVec.ult ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

/-- HOL `riscv$dfn'BLT` (`dfn'BLT_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BLT_def"]
def «dfn'BLT» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((BitVec.slt ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

/-- HOL `riscv$dfn'BGEU` (`dfn'BGEU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BGEU_def"]
def «dfn'BGEU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((!(BitVec.ult ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0)))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

/-- HOL `riscv$dfn'BGE` (`dfn'BGE_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BGE_def"]
def «dfn'BGE» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((BitVec.sle ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))) ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

/-- HOL `riscv$dfn'BEQ` (`dfn'BEQ_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BEQ_def"]
def «dfn'BEQ» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) == ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

/-- HOL `riscv$dfn'XOR` (`dfn'XOR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'XOR_def"]
def «dfn'XOR» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) ^^^ (GPR rs2 state))), rd)) state))

/-- HOL `riscv$dfn'SUBW` (`dfn'SUBW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SUBW_def"]
def «dfn'SUBW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) - ((holWordExtract 32 31 0 (GPR rs2 s))))))), rd)) s)))))

/-- HOL `riscv$dfn'SUB` (`dfn'SUB_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SUB_def"]
def «dfn'SUB» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) - (GPR rs2 state))), rd)) state))

/-- HOL `riscv$dfn'SLTU` (`dfn'SLTU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SLTU_def"]
def «dfn'SLTU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => («write'GPR» ((((holV2w 64 ((((BitVec.ult ((if v then ((BitVec.setWidth 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) ((if v0 then ((BitVec.setWidth 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))) :: (([] : (List Bool))))))), rd)) s0))))

/-- HOL `riscv$dfn'SLT` (`dfn'SLT_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SLT_def"]
def «dfn'SLT» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => («write'GPR» ((((holV2w 64 ((((BitVec.slt ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))) :: (([] : (List Bool))))))), rd)) s0))))

/-- HOL `riscv$dfn'OR` (`dfn'OR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'OR_def"]
def «dfn'OR» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) ||| (GPR rs2 state))), rd)) state))

/-- HOL `riscv$dfn'AND` (`dfn'AND_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AND_def"]
def «dfn'AND» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) &&& (GPR rs2 state))), rd)) state))

/-- HOL `riscv$dfn'ADDW` (`dfn'ADDW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ADDW_def"]
def «dfn'ADDW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) + ((holWordExtract 32 31 0 (GPR rs2 s))))))), rd)) s)))))

/-- HOL `riscv$dfn'ADD` (`dfn'ADD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ADD_def"]
def «dfn'ADD» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) + (GPR rs2 state))), rd)) state))

/-- HOL `riscv$dfn'XORI` (`dfn'XORI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'XORI_def"]
def «dfn'XORI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) ^^^ (BitVec.signExtend 64 imm))), rd)) state))

/-- HOL `riscv$dfn'SLTIU` (`dfn'SLTIU_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SLTIU_def"]
def «dfn'SLTIU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => («write'GPR» ((((holV2w 64 ((((BitVec.ult ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) (BitVec.signExtend 64 imm))) :: (([] : (List Bool))))))), rd)) s)))

/-- HOL `riscv$dfn'SLTI` (`dfn'SLTI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SLTI_def"]
def «dfn'SLTI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => («write'GPR» ((((holV2w 64 ((((BitVec.slt ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) (BitVec.signExtend 64 imm))) :: (([] : (List Bool))))))), rd)) s)))

/-- HOL `riscv$dfn'ORI` (`dfn'ORI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ORI_def"]
def «dfn'ORI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) ||| (BitVec.signExtend 64 imm))), rd)) state))

/-- HOL `riscv$dfn'LUI` (`dfn'LUI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LUI_def"]
def «dfn'LUI» (arg0 : ((BitVec 5) × (BitVec 20))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, imm) =>
  (fun (state : riscv_state) => («write'GPR» ((((BitVec.signExtend 64 ((BitVec.setWidth 32 (imm ++ (BitVec.ofNat 12 0)))))), rd)) state))

/-- HOL `riscv$dfn'AUIPC` (`dfn'AUIPC_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AUIPC_def"]
def «dfn'AUIPC» (arg0 : ((BitVec 5) × (BitVec 20))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, imm) =>
  (fun (state : riscv_state) => («write'GPR» (((((PC state) + ((BitVec.signExtend 64 ((BitVec.setWidth 32 (imm ++ (BitVec.ofNat 12 0)))))))), rd)) state))

/-- HOL `riscv$dfn'ANDI` (`dfn'ANDI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ANDI_def"]
def «dfn'ANDI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) &&& (BitVec.signExtend 64 imm))), rd)) state))

/-- HOL `riscv$dfn'ADDIW` (`dfn'ADDIW_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ADDIW_def"]
def «dfn'ADDIW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 (((GPR rs1 s) + (BitVec.signExtend 64 imm))))))), rd)) s)))))

/-- HOL `riscv$dfn'ADDI` (`dfn'ADDI_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ADDI_def"]
def «dfn'ADDI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) + (BitVec.signExtend 64 imm))), rd)) state))

/-- HOL `riscv$write'ReserveLoad` (`write'ReserveLoad_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'ReserveLoad_def"]
def «write'ReserveLoad» (value : (Option (BitVec 64))) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_ReserveLoad := ((fun (_eta1 : ((BitVec 8) → (Option (BitVec 64)))) => (holUpdate state.procID value state.c_ReserveLoad))) r.c_ReserveLoad }))

/-- HOL `riscv$ReserveLoad` (`ReserveLoad_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "ReserveLoad_def"]
def ReserveLoad (state : riscv_state) : (Option (BitVec 64)) :=
  (state.c_ReserveLoad state.procID)

/-- HOL `riscv$matchLoadReservation` (`matchLoadReservation_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "matchLoadReservation_def"]
noncomputable def matchLoadReservation (vAddr : (BitVec 64)) : (riscv_state → Bool) :=
  (fun (state : riscv_state) => (((ReserveLoad state).isSome) && ((((holThe (ReserveLoad state))) == vAddr))))

/-- HOL `riscv$dfn'SC_W` (`dfn'SC_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SC_W_def"]
noncomputable def «dfn'SC_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((if ((!(matchLoadReservation v state))) then ((«write'GPR» (((BitVec.ofNat 64 1), rd)) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => («write'ReserveLoad» ((none : (Option (BitVec 64)))) ((«write'GPR» (((BitVec.ofNat 64 0), rd)) ((rawWriteData ((pAddr, (((GPR rs2 s), 4)))) s)))))))))))))

/-- HOL `riscv$dfn'SC_D` (`dfn'SC_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SC_D_def"]
noncomputable def «dfn'SC_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 64) := (GPR rs1 s); (if ((!(((holWordExtract 3 2 0 v_1) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v_1) s)) else ((if ((!(matchLoadReservation v_1 s))) then ((«write'GPR» (((BitVec.ofNat 64 1), rd)) s)) else ((match (translateAddr ((v_1, (fetchType.Data, accessType.Read))) s) with | (v0, s_1) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v_1) s_1) | some pAddr => («write'ReserveLoad» ((none : (Option (BitVec 64)))) ((«write'GPR» (((BitVec.ofNat 64 0), rd)) ((rawWriteData ((pAddr, (((GPR rs2 s_1), 8)))) s_1))))))))))))))))

/-- HOL `riscv$dfn'LR_W` (`dfn'LR_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LR_W_def"]
def «dfn'LR_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × (BitVec 5))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, rs1))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'ReserveLoad» (some v) ((«write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s))))), rd)) s)))))))))

/-- HOL `riscv$dfn'LR_D` (`dfn'LR_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LR_D_def"]
def «dfn'LR_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × (BitVec 5))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, rs1))) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 64) := (GPR rs1 s); (if ((!(((holWordExtract 3 2 0 v_1) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v_1) s)) else ((match (translateAddr ((v_1, (fetchType.Data, accessType.Read))) s) with | (v0, s_1) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v_1) s_1) | some pAddr => («write'ReserveLoad» (some v_1) ((«write'GPR» (((rawReadData pAddr s_1), rd)) s_1))))))))))))

/-- HOL `riscv$dfn'AMOXOR_W` (`dfn'AMOXOR_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOXOR_W_def"]
def «dfn'AMOXOR_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, (((((GPR rs2 s) ^^^ v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOXOR_D` (`dfn'AMOXOR_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOXOR_D_def"]
def «dfn'AMOXOR_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, (((((GPR rs2 s) ^^^ v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOSWAP_W` (`dfn'AMOSWAP_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOSWAP_W_def"]
def «dfn'AMOSWAP_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s), 4)))) ((«write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s))))), rd)) s)))))))))

/-- HOL `riscv$dfn'AMOSWAP_D` (`dfn'AMOSWAP_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOSWAP_D_def"]
def «dfn'AMOSWAP_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s), 8)))) ((«write'GPR» (((rawReadData pAddr s), rd)) s)))))))))

/-- HOL `riscv$dfn'AMOOR_W` (`dfn'AMOOR_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOOR_W_def"]
def «dfn'AMOOR_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, (((((GPR rs2 s) ||| v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOOR_D` (`dfn'AMOOR_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOOR_D_def"]
def «dfn'AMOOR_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, (((((GPR rs2 s) ||| v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOMIN_W` (`dfn'AMOMIN_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMIN_W_def"]
def «dfn'AMOMIN_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, ((((if BitVec.slt (GPR rs2 s) v_1 then (GPR rs2 s) else v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOMIN_D` (`dfn'AMOMIN_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMIN_D_def"]
def «dfn'AMOMIN_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, ((((if BitVec.slt (GPR rs2 s) v_1 then (GPR rs2 s) else v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOMINU_W` (`dfn'AMOMINU_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMINU_W_def"]
def «dfn'AMOMINU_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, ((((if BitVec.ult (GPR rs2 s) v_1 then (GPR rs2 s) else v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOMINU_D` (`dfn'AMOMINU_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMINU_D_def"]
def «dfn'AMOMINU_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, ((((if BitVec.ult (GPR rs2 s) v_1 then (GPR rs2 s) else v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOMAX_W` (`dfn'AMOMAX_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMAX_W_def"]
def «dfn'AMOMAX_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, ((((if BitVec.slt (GPR rs2 s) v_1 then v_1 else (GPR rs2 s))), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOMAX_D` (`dfn'AMOMAX_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMAX_D_def"]
def «dfn'AMOMAX_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, ((((if BitVec.slt (GPR rs2 s) v_1 then v_1 else (GPR rs2 s))), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOMAXU_W` (`dfn'AMOMAXU_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMAXU_W_def"]
def «dfn'AMOMAXU_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, ((((if BitVec.ult (GPR rs2 s) v_1 then v_1 else (GPR rs2 s))), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOMAXU_D` (`dfn'AMOMAXU_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMAXU_D_def"]
def «dfn'AMOMAXU_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, ((((if BitVec.ult (GPR rs2 s) v_1 then v_1 else (GPR rs2 s))), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOAND_W` (`dfn'AMOAND_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOAND_W_def"]
def «dfn'AMOAND_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, (((((GPR rs2 s) &&& v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOAND_D` (`dfn'AMOAND_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOAND_D_def"]
def «dfn'AMOAND_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, (((((GPR rs2 s) &&& v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOADD_W` (`dfn'AMOADD_W_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOADD_W_def"]
def «dfn'AMOADD_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, (((((GPR rs2 s) + v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$dfn'AMOADD_D` (`dfn'AMOADD_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOADD_D_def"]
def «dfn'AMOADD_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, (((((GPR rs2 s) + v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- HOL `riscv$write'PC` (`write'PC_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'PC_def"]
def «write'PC» (value : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_PC := ((fun (_eta1 : ((BitVec 8) → (BitVec 64))) => (holUpdate state.procID value state.c_PC))) r.c_PC }))

/-- HOL `riscv_step$update_pc` (`update_pc_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "update_pc_def"]
def update_pc (v : (BitVec 64)) (s : riscv_state) : (Option riscv_state) :=
  (some («write'PC» v s))

/-- HOL `riscv$NextFetch` (`NextFetch_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "NextFetch_def"]
def NextFetch (state : riscv_state) : (Option TransferControl) :=
  (state.c_NextFetch state.procID)


end Flapjack.RiscV.L3
