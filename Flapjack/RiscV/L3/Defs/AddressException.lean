import Flapjack.RiscV.L3.Defs
namespace Flapjack.RiscV.L3

/-- Source review: riscvScript3460-3472 passes the original exception and
SOME original virtual address to setTrap on the supplied full state. setTrap
3433-3459 constructs the original two-field synchronous trap and writes only
current-core NextFetch. The canonical arbitrary intermediate trap is retained;
both fields are then overwritten. No core-bound or successful-address premise.
This is independent of the full model's still-open instruction assembly. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "signalAddressException_def"]
noncomputable def signalAddressException (arg0 : (ExceptionType × (BitVec 64))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (e, vAddr) =>
  (fun (state : riscv_state) => (setTrap ((e, (some vAddr))) state))

end Flapjack.RiscV.L3
