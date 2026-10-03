import Flapjack.RiscV.L3.Defs.MMU.TLB
set_option maxRecDepth 200000
namespace Flapjack.RiscV.L3

/-- Source review: riscvScript5079-5385, complete sixteen-slot FOR scan. The
six-component accumulator retains found-empty, candidate index, minimum age,
updated table, new entry, and native state. Some uses strict unsigned age
comparison and changes only candidate/minimum; None fills only the first empty
slot. The initial candidate is zero and minimum is sign-extended one-bit one,
so a full all-maximum-age table replaces slot zero. Final replacement occurs
only when no empty slot was filled. mkTLBEntry retains arbitrary level and
current-core age; no core, address, level or table restriction is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "addToTLB_def"]
noncomputable def addToTLB (arg0 : ((BitVec 6) × ((BitVec 64) × ((BitVec 64) × (SV_PTE × ((BitVec 64) × (Nat × (Bool × ((BitVec 4) → (Option TLBEntry)))))))))) : (riscv_state → ((BitVec 4) → (Option TLBEntry))) :=
  match arg0 with
  | (asid, (vAddr, (pAddr, (pte, (pteAddr, (i, (global, curTLB))))))) =>
  (fun (state : riscv_state) => (let s : (Bool × (Nat × ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state))))) := (((holFor ((0, (((TLBEntries - 1), ((fun (i_1 : Nat) => (fun (state_1 : (Bool × (Nat × ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state)))))) => (match (state_1.2.2.2.1 (BitVec.ofNat 4 i_1)) with | none => ((), ((if (!state_1.1) then ((true, ((let s0 : (Nat × ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state)))) := state_1.2; (s0.1, ((let s0_1 : ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state))) := s0.2; (s0_1.1, ((((holUpdate (BitVec.ofNat 4 i_1) (some state_1.2.2.2.2.1) state_1.2.2.2.1)), s0_1.2.2)))))))))) else state_1))) | some e => (if (BitVec.ult e.age state_1.2.2.1) then ((let s : (Bool × (Nat × ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state))))) := (state_1.1, ((let s : (Nat × ((BitVec 64) × (((BitVec 4) → (Option TLBEntry)) × (TLBEntry × riscv_state)))) := state_1.2; (s.1, (e.age, s.2.2))))); ((), ((s.1, (i_1, s.2.2)))))) else (((), state_1)))))))))))) ((false, ((0, ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))), ((curTLB, ((((mkTLBEntry ((asid, ((global, ((vAddr, ((pAddr, ((pte, (i, pteAddr))))))))))) state)), state)))))))))))).2; (if (!s.1) then ((holUpdate (BitVec.ofNat 4 s.2.1) (some s.2.2.2.2.1) s.2.2.2.1)) else s.2.2.2.1)))

end Flapjack.RiscV.L3
