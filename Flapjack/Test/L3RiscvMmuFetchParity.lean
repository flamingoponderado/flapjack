import Flapjack.RiscV.L3.Defs

/-! Kernel replay of the original native model MMU/Fetch/memory EVAL rows.
The fixture supplies exactly the fields read by these original branches;
unread source ARB fields are represented by arbitrary native default fields.
This regression coverage is not a HOL-to-Lean equivalence proof or a full
Run/NextRISCV port. -/
namespace Flapjack.Test.L3RiscvMmuFetchParity
open Flapjack.RiscV.L3

private def state : riscv_state :=
  { (default : riscv_state) with
    procID := 0
    exception := .NoException
    MEM8 := fun a => BitVec.ofNat 8 a.toNat
    c_PC := fun _ => 0
    c_Skip := fun _ => 0
    c_gpr := fun _ r => if r = 2 then 8 else 0
    c_MCSR := fun _ =>
      { (default : MachineCSR) with
        mstatus := { (default : mstatus) with VM := 0, MMPRV := false, MPRV := 3 }
        mcpuid := { (default : mcpuid) with ArchBase := 2 } } }

example : rawReadData 0 state = 0x0706050403020100 := by decide
example : rawReadData 3 state = 0x0a09080706050403 := by decide
example : rawReadData 7 state = 0x0e0d0c0b0a090807 := by decide
example : (translateAddr (0x12345, .Data, .Read) state).1 = some 0x12345 := by decide
example : (walk64 (0, .Data, .Read, .Machine, 0, 0) state).1 = none := by
  rw [walk64]
  decide
example : (walk64 (0, .Data, .Read, .Machine, 0, 2) state).1 = none := by
  rw [walk64]
  decide
example : (Fetch state).1 = .Half 256 := by decide
example : Skip (Fetch state).2 = 2 := by decide

private def wordState : riscv_state :=
  { state with MEM8 := fun a => if a = 0 then 3 else BitVec.ofNat 8 a.toNat }
example : (Fetch wordState).1 = .Word 0x03020103 := by decide
example : Skip (Fetch wordState).2 = 4 := by decide
example : GPR 1 («dfn'LD» (1, 2, 0) state) = 0x0f0e0d0c0b0a0908 := by decide
example : rawReadData 7 (rawWriteData (7, 0xabcd, 2) state) =
    0x0e0d0c0b0a09abcd := by decide

end Flapjack.Test.L3RiscvMmuFetchParity
