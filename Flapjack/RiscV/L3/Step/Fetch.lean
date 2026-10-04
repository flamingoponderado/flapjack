import Flapjack.RiscV.L3.Defs.ReadInst
import Flapjack.RiscV.L3.Defs.MMU.Translate

namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

/-- Source review: riscv_stepScript.sml:28-32 translates the current PC for
Instruction/Read, then reads the returned state at THE of the optional address.
This is the step evaluator's Fetch, distinct from model Fetch. THE NONE retains
HOL's canonical unspecified choice; no successful-translation premise is added. -/
noncomputable def Fetch (s : riscv_state) : rawInstType × riscv_state :=
  match translateAddr (PC s, fetchType.Instruction, accessType.Read) s with
  | (w, s₁) => rawReadInst (holThe w) s₁

end Flapjack.RiscV.L3.Step
