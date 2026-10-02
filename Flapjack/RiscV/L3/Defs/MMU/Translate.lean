import Flapjack.RiscV.L3.Defs.MMU.Walk
import Flapjack.RiscV.L3.Defs.MMU.Insert
namespace Flapjack.RiscV.L3

/-- Source review: riscvScript5491-5623 complete hit/miss equation. Current
ASID and current-core TLB select the first matching entry. A hit checks permission,
retains its returned state, and combines physical base with masked virtual offset.
Only a Write hit with D=false sets D, writes exactly eight PTE bytes, and updates
the same TLB index; R and age remain unchanged. Failure forwards None and the
permission-returned state. A miss walks from original SCSR.sptbr at the supplied
level, forwards a failed walk state, or inserts the entire successful result into
the returned state's TLB using the original ASID. No hit, permission, alignment,
level or core-bound hypothesis is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "translate64_def"]
noncomputable def translate64 (arg0 : ((BitVec 64) × (fetchType × (accessType × (Privilege × Nat))))) : (riscv_state → ((Option (BitVec 64)) × riscv_state)) :=
  match arg0 with
  | (vAddr, (ft, (ac, (priv, level)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 6) := (curASID () state); (match (lookupTLB ((v, ((vAddr, (TLB state)))))) with | none => (match (walk64 ((vAddr, ((ft, ((ac, ((priv, ((((SCSR state).sptbr), level)))))))))) state) with | (v0, s) => (match v0 with | none => (((none : (Option (BitVec 64)))), s) | some v1 => (match v1 with | (pAddr, v3) => (match v3 with | (pte, v5) => (match v5 with | (i, v7) => (match v7 with | (global, pteAddr) => ((some pAddr), ((«write'TLB» ((addToTLB ((v, ((vAddr, ((pAddr, ((pte, ((pteAddr, ((i, ((global, (TLB s))))))))))))))) s)) s))))))))) | some v2 => (match v2 with | (e, idx) => (match (checkMemPermission ((ft, ((ac, (priv, e.pte.PTE_T))))) state) with | (v_1, s) => (if v_1 then ((((some ((e.pAddr ||| (vAddr &&& e.vAddrMask))))), ((if (((ac == accessType.Write) && (!e.pte.PTE_D))) then ((let s0 : TLBEntry := (let r := e; { r with pte := ((fun (_eta1 : SV_PTE) => ((let r := e.pte; { r with PTE_D := ((fun (_eta1 : Bool) => true)) r.PTE_D })))) r.pte }); (let s1 : riscv_state := (rawWriteData ((s0.pteAddr, (((«reg'SV_PTE» s0.pte), 8)))) s); («write'TLB» ((holUpdate idx (some s0) (TLB s1))) s1)))) else s)))) else ((((none : (Option (BitVec 64)))), s))))))))

/-- Source review: riscvScript5624-5691 complete wrapper. MMPRV selects
MPRV1 only for Data; other cases use MPRV. The VM selector always calls vmType
and retains its returned state. Mbare and any Machine pair return the original
address; Sv39 and Sv48 call exact translate64 at levels two and three. Other
pairs return None. Invalid VM selectors retain vmType's original exception and
canonical unspecified VM result; no preferred mode or default is introduced.
All native carriers, fixed word widths, arbitrary addresses and core maps remain
unchanged, with no alignment, privilege or successful-translation premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "translateAddr_def"]
noncomputable def translateAddr (arg0 : ((BitVec 64) × (fetchType × accessType))) : (riscv_state → ((Option (BitVec 64)) × riscv_state)) :=
  match arg0 with
  | (vAddr, (ft, ac)) =>
  (fun (state : riscv_state) => (let v : Privilege := (privilege ((if (((((MCSR state).mstatus).MMPRV) && (ft == fetchType.Data))) then (((MCSR state).mstatus).MPRV1) else (((MCSR state).mstatus).MPRV)))); (match (match (vmType (((MCSR state).mstatus).VM) state) with | (v0, s) => ((v0, v), s)) with | (v0, s) => (match v0 with | (v1, v2) => (match v1 with | .Mbare => ((some vAddr), s) | .Mbb => (match v2 with | .User => (((none : (Option (BitVec 64)))), s) | .Supervisor => (((none : (Option (BitVec 64)))), s) | .Hypervisor => (((none : (Option (BitVec 64)))), s) | .Machine => ((some vAddr), s)) | .Mbbid => (match v2 with | .User => (((none : (Option (BitVec 64)))), s) | .Supervisor => (((none : (Option (BitVec 64)))), s) | .Hypervisor => (((none : (Option (BitVec 64)))), s) | .Machine => ((some vAddr), s)) | .Sv32 => (match v2 with | .User => (((none : (Option (BitVec 64)))), s) | .Supervisor => (((none : (Option (BitVec 64)))), s) | .Hypervisor => (((none : (Option (BitVec 64)))), s) | .Machine => ((some vAddr), s)) | .Sv39 => (match v2 with | .User => (translate64 ((vAddr, ((ft, ((ac, (v, 2))))))) s) | .Supervisor => (translate64 ((vAddr, ((ft, ((ac, (v, 2))))))) s) | .Hypervisor => (translate64 ((vAddr, ((ft, ((ac, (v, 2))))))) s) | .Machine => ((some vAddr), s)) | .Sv48 => (match v2 with | .User => (translate64 ((vAddr, ((ft, ((ac, (v, 3))))))) s) | .Supervisor => (translate64 ((vAddr, ((ft, ((ac, (v, 3))))))) s) | .Hypervisor => (translate64 ((vAddr, ((ft, ((ac, (v, 3))))))) s) | .Machine => ((some vAddr), s)) | .Sv57 => (match v2 with | .User => (((none : (Option (BitVec 64)))), s) | .Supervisor => (((none : (Option (BitVec 64)))), s) | .Hypervisor => (((none : (Option (BitVec 64)))), s) | .Machine => ((some vAddr), s)) | .Sv64 => (match v2 with | .User => (((none : (Option (BitVec 64)))), s) | .Supervisor => (((none : (Option (BitVec 64)))), s) | .Hypervisor => (((none : (Option (BitVec 64)))), s) | .Machine => ((some vAddr), s)))))))


end Flapjack.RiscV.L3
