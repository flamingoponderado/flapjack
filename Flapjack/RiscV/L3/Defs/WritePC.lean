import Flapjack.RiscV.L3.Defs.ReadInst

/-! Complete original current-core PC writer. The state carrier is unchanged;
no totalCore bound is imposed on the word8 function key. -/
namespace Flapjack.RiscV.L3

def «write'PC» (value : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_PC := ((fun (_eta1 : ((BitVec 8) → (BitVec 64))) => (holUpdate state.procID value state.c_PC))) r.c_PC }))

/-- Flapjack kernel check of the complete original record update. No distinct
named HOL theorem is claimed; the source definition above supplies the shape. -/
theorem writePC_fullRecord (value : BitVec 64) (s : riscv_state) :
    «write'PC» value s = { s with c_PC := holUpdate s.procID value s.c_PC } := rfl

/-- Flapjack whole-key check; includes the current core and every other key
without bounds or success assumptions. Not a separate named HOL port. -/
theorem writePC_allKeys (value : BitVec 64) (s : riscv_state) (core : BitVec 8) :
    («write'PC» value s).c_PC core =
      if core = s.procID then value else s.c_PC core := by
  simp [«write'PC», holUpdate, eq_comm]

/-- Flapjack generic current-PC observation of the complete record writer. -/
theorem writePC_current (value : BitVec 64) (s : riscv_state) :
    PC («write'PC» value s) = value := by
  simp [PC, «write'PC», holUpdate]

end Flapjack.RiscV.L3
