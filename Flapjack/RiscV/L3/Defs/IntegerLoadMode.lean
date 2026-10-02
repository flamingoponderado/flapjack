import Flapjack.RiscV.L3.Defs.MMU.Exception
import Flapjack.RiscV.L3.Defs
import Flapjack.RiscV.L3.Defs.MMU.Primitives
namespace Flapjack.RiscV.L3
open Flapjack.Basis.Pure.MlString

/-! Complete integer-load mode dependency: source architecture397-415,
curArch1417-1429 and in32BitMode1430-1440. All two-bit selectors retained;
invalid1 raises the exact UNDEFINED message and returns canonical arbitrary
Architecture, preserving the updated state. No default architecture/Boolean,
valid-selector premise, core bound or whole-instruction acceptance is supplied. -/

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "architecture_def"]
noncomputable def architecture (ab : (BitVec 2)) : (riscv_state → (Architecture × riscv_state)) :=
  (fun (state : riscv_state) => (((fun (v : (BitVec 2)) => (if ((v == (BitVec.ofNat 2 0))) then (Architecture.RV32I, state) else ((if ((v == (BitVec.ofNat 2 2))) then (Architecture.RV64I, state) else ((if ((v == (BitVec.ofNat 2 3))) then (Architecture.RV128I, state) else (((«raise'exception» (Ta := Architecture)) ((exception.UNDEFINED (((((BitVec.ofNat 8 85) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 107) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 111) :: (((BitVec.ofNat 8 119) :: (((BitVec.ofNat 8 110) :: (((BitVec.ofNat 8 32) :: (((BitVec.ofNat 8 97) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 99) :: (((BitVec.ofNat 8 104) :: (((BitVec.ofNat 8 105) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 99) :: (((BitVec.ofNat 8 116) :: (((BitVec.ofNat 8 117) :: (((BitVec.ofNat 8 114) :: (((BitVec.ofNat 8 101) :: (((BitVec.ofNat 8 58) :: (((BitVec.ofNat 8 32) :: (([] : (List HolChar))))))))))))))))))))))))))))))))))))))))))))))) ++ (holNumToDecString ab.toNat))))) state))))))))) ab))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "curArch_def"]
noncomputable def curArch (_u_ : Unit) : (riscv_state → (Architecture × riscv_state)) :=
  (fun (state : riscv_state) => (architecture (((MCSR state).mcpuid).ArchBase) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "in32BitMode_def"]
noncomputable def in32BitMode (_u_ : Unit) : (riscv_state → (Bool × riscv_state)) :=
  (fun (state : riscv_state) => (match (curArch () state) with | (v, s) => ((v == Architecture.RV32I), s)))

end Flapjack.RiscV.L3
