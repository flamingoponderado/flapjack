import Flapjack.RiscV.L3.Support
namespace Flapjack.RiscV.L3

/-! Complete original reservation primitives for load-reserved/store-conditional.
Source1381-1398 reads/updates the current core optional word64 virtual address;
5691-5702 matches IsSome and THE equality. Canonical THE NONE is retained and
masked by the IsSome conjunction, never replaced with a chosen address. No
core bound, existing-reservation or valid-address premise; no atomic/Run/Next
assembly claim. These ATy function fields are not HOL finite-map translations. -/

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'ReserveLoad_def"]
def «write'ReserveLoad» (value : (Option (BitVec 64))) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_ReserveLoad := ((fun (_eta1 : ((BitVec 8) → (Option (BitVec 64)))) => (holUpdate state.procID value state.c_ReserveLoad))) r.c_ReserveLoad }))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "ReserveLoad_def"]
def ReserveLoad (state : riscv_state) : (Option (BitVec 64)) :=
  (state.c_ReserveLoad state.procID)

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "matchLoadReservation_def"]
noncomputable def matchLoadReservation (vAddr : (BitVec 64)) : (riscv_state → Bool) :=
  (fun (state : riscv_state) => (((ReserveLoad state).isSome) && ((((holThe (ReserveLoad state))) == vAddr))))

end Flapjack.RiscV.L3
