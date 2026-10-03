import Flapjack.RiscV.L3.Defs.MMU.Access
import Flapjack.RiscV.L3.Defs
import Flapjack.RiscV.L3.Defs.MMU.Insert
namespace Flapjack.RiscV.L3

/-- Literal complete original TLB flush/fence equation. The flush traverses
the original TLBEntries range of all 16 word4 slots, including slot15. ASID zero
includes global entries; a matching nonzero ASID clears only non-global entries.
Optional virtual address uses the entry mask. SFENCE register zero omits the
address filter; other registers use logical GPR and only the current core TLB
is updated. No success, well-formed-entry or core-bound premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "flushTLB_def"]
noncomputable def flushTLB (arg0 : ((BitVec 6) × ((Option (BitVec 64)) × ((BitVec 4) → (Option TLBEntry))))) : ((BitVec 4) → (Option TLBEntry)) :=
  match arg0 with
  | (asid, (addr, curTLB)) =>
  ((((holFor ((0, (((TLBEntries - 1), ((fun (i : Nat) => (fun (state : (((BitVec 4) → (Option TLBEntry)) × Unit)) => (match (((state.1 (BitVec.ofNat 4 i))), addr) with | (v, v1) => (match v with | none => ((), state) | some e => (match v1 with | none => ((), ((if ((((asid == (BitVec.ofNat 6 0))) || (((asid == e.asid) && (!e.global))))) then ((((holUpdate (BitVec.ofNat 4 i) ((none : (Option TLBEntry))) state.1)), ())) else state))) | some va => ((), ((if ((((((asid == (BitVec.ofNat 6 0))) || (((asid == e.asid) && (!e.global))))) && ((e.vAddr == (va &&& e.vMatchMask))))) then ((((holUpdate (BitVec.ofNat 4 i) ((none : (Option TLBEntry))) state.1)), ())) else state)))))))))))))) ((curTLB, ())))).2).1

/-- Literal complete original TLB flush/fence equation. The flush traverses
the original TLBEntries range of all 16 word4 slots, including slot15. ASID zero
includes global entries; a matching nonzero ASID clears only non-global entries.
Optional virtual address uses the entry mask. SFENCE register zero omits the
address filter; other registers use logical GPR and only the current core TLB
is updated. No success, well-formed-entry or core-bound premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SFENCE_VM_def"]
noncomputable def «dfn'SFENCE_VM» (rs1 : (BitVec 5)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => («write'TLB» ((flushTLB ((((curASID () state)), ((((if ((rs1 == (BitVec.ofNat 5 0))) then ((none : (Option (BitVec 64)))) else ((some (GPR rs1 state))))), (TLB state))))))) state))

/-- Flapjack-only unconditional whole-state normal form; no separate HOL original. -/
theorem sfenceVMWholeState (rs1 : BitVec 5) (s : riscv_state) :
    «dfn'SFENCE_VM» rs1 s = «write'TLB»
      (flushTLB (curASID () s,
        (if rs1 == 0 then none else some (GPR rs1 s)),TLB s)) s := by
  rfl

end Flapjack.RiscV.L3
