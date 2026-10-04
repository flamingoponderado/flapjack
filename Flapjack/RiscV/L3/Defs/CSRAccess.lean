import Flapjack.RiscV.L3.Defs.IntegerLoadMode
import Flapjack.RiscV.L3.Defs.MMU.Primitives
namespace Flapjack.RiscV.L3

/-! Compatibility queries for retained ordinary CSR records. Availability is an
explicit whitelist that excludes floating-point, hardware timers, interrupts and
paging. The integer privilege/permission selectors retain their original equations;
privileged CSR instructions themselves are absent from the riscv-mi AST. -/

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "privLevel_def"]
def privLevel (p : Privilege) : (BitVec 2) :=
  (match p with | .User => (BitVec.ofNat 2 0) | .Supervisor => (BitVec.ofNat 2 1) | .Hypervisor => (BitVec.ofNat 2 2) | .Machine => (BitVec.ofNat 2 3))

/-- Availability of the retained ordinary CSR record helpers. Privileged CSR
instructions have no constructors in riscv-mi; this compatibility query excludes
floating-point controls, hardware counters/timers, interrupts and paging. -/
def is_CSR_defined (csr : BitVec 12) (state : riscv_state) : Bool × riscv_state :=
  (decide (csr.toNat ∈ [256, 257, 320, 321, 3394, 3395, 512, 513, 576, 577, 578, 579, 3840, 3841, 3856, 768, 769, 832, 833, 834, 835, 896, 897, 898, 899, 900, 901, 1920, 1921]), state)

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
