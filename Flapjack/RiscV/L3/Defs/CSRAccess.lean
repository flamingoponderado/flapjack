import Flapjack.RiscV.L3.Defs.IntegerLoadMode
import Flapjack.RiscV.L3.Defs.MMU.Primitives
namespace Flapjack.RiscV.L3

/-! Complete literal CSR access section. CSR ranges use HOL signed word12
comparisons; permission privilege uses unsigned word2 comparison. MPRV is
the original selector. Mode checks forward all returned state, including
unspecified architecture and pre-existing exceptions. checkCSROp ignores rs1.
No address-validity, core-bound, architecture or successful-access premise. -/

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "privLevel_def"]
def privLevel (p : Privilege) : (BitVec 2) :=
  (match p with | .User => (BitVec.ofNat 2 0) | .Supervisor => (BitVec.ofNat 2 1) | .Hypervisor => (BitVec.ofNat 2 2) | .Machine => (BitVec.ofNat 2 3))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "is_CSR_defined_def"]
noncomputable def is_CSR_defined (csr : (BitVec 12)) : (riscv_state → (Bool × riscv_state)) :=
  (fun (state : riscv_state) => (if ((((BitVec.sle (BitVec.ofNat 12 1) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 3))))) then (true, state) else ((if ((((BitVec.sle (BitVec.ofNat 12 3072) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 3074))))) then (true, state) else ((match (if ((BitVec.sle (BitVec.ofNat 12 3200) csr)) then ((if ((BitVec.sle csr (BitVec.ofNat 12 3202))) then ((in32BitMode () state)) else (false, state))) else (false, state)) with | (v, s) => (if v then (true, s) else ((if ((((BitVec.sle (BitVec.ofNat 12 256) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 257))))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 260))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 289))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 3329))) then (true, s) else ((match (if ((csr == (BitVec.ofNat 12 3457))) then ((in32BitMode () s)) else (false, s)) with | (v_1, s_1) => (if v_1 then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 320) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 321))))) then (true, s_1) else ((if ((csr == (BitVec.ofNat 12 324))) then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 3394) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 3395))))) then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 384) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 385))))) then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 2304) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 2306))))) then (true, s_1) else ((match (if ((BitVec.sle (BitVec.ofNat 12 2432) csr)) then ((if ((BitVec.sle csr (BitVec.ofNat 12 2434))) then ((in32BitMode () s_1)) else (false, s_1))) else (false, s_1)) with | (v, s) => (if v then (true, s) else ((if ((((BitVec.sle (BitVec.ofNat 12 3840) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 3841))))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 3856))) then (true, s) else ((if ((((BitVec.sle (BitVec.ofNat 12 768) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 770))))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 772))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 801))) then (true, s) else ((if ((csr == (BitVec.ofNat 12 1793))) then (true, s) else ((match (if ((csr == (BitVec.ofNat 12 1857))) then ((in32BitMode () s)) else (false, s)) with | (v_1, s_1) => (if v_1 then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 832) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 836))))) then (true, s_1) else ((if ((((BitVec.sle (BitVec.ofNat 12 896) csr)) && ((BitVec.sle csr (BitVec.ofNat 12 901))))) then (true, s_1) else ((if ((BitVec.sle (BitVec.ofNat 12 2817) csr)) then (true, s_1) else ((match (if ((csr == (BitVec.ofNat 12 2945))) then ((in32BitMode () s_1)) else (false, s_1)) with | (v, s) => (((v || ((((BitVec.sle (BitVec.ofNat 12 1920) csr)) && ((((BitVec.sle csr (BitVec.ofNat 12 1923))) && ((!((csr == (BitVec.ofNat 12 1922))))))))))), s)))))))))))))))))))))))))))))))))))))))))))))))))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "curPrivilege_def"]
noncomputable def curPrivilege (_u_ : Unit) : (riscv_state → Privilege) :=
  (fun (state : riscv_state) => (privilege (((MCSR state).mstatus).MPRV)))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "csrPR_def"]
def csrPR (csr : (BitVec 12)) : (BitVec 2) :=
  (holWordExtract 2 9 8 csr)

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "csrRW_def"]
def csrRW (csr : (BitVec 12)) : (BitVec 2) :=
  (holWordExtract 2 11 10 csr)

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "check_CSR_access_def"]
def check_CSR_access (arg0 : ((BitVec 2) × ((BitVec 2) × (Privilege × accessType)))) : Bool :=
  match arg0 with
  | (rw, (pr, (p, a))) =>
  ((((a == accessType.Read) || ((!((rw == (BitVec.ofNat 2 3))))))) && ((!(BitVec.ult (privLevel p) pr))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "checkCSROp_def"]
noncomputable def checkCSROp (arg0 : ((BitVec 12) × ((BitVec 5) × accessType))) : (riscv_state → (Bool × riscv_state)) :=
  match arg0 with
  | (csr, (_rs1, a)) =>
  (fun (state : riscv_state) => (match (is_CSR_defined csr state) with | (v, s) => (((v && ((check_CSR_access (((csrRW csr), (((csrPR csr), ((((curPrivilege () s)), a)))))))))), s)))

/-- Flapjack-only ignored-operand normal form; no separate HOL original. -/
theorem checkCSROpIgnoresRs1 (csr : BitVec 12) (r1 r2 : BitVec 5)
    (a : accessType) (s : riscv_state) :
    checkCSROp (csr,r1,a) s = checkCSROp (csr,r2,a) s := by rfl

/-- Flapjack-only exact returned-state normal form; no separate HOL original. -/
theorem checkCSROpState (csr : BitVec 12) (rs : BitVec 5)
    (a : accessType) (s : riscv_state) :
    (checkCSROp (csr,rs,a) s).2 = (is_CSR_defined csr s).2 := by
  simp only [checkCSROp]

end Flapjack.RiscV.L3
