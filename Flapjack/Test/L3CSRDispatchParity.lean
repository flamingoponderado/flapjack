import Flapjack.RiscV.L3.Defs.CSRDispatch
namespace Flapjack.Test.L3CSRDispatchParity
open Flapjack.RiscV.L3

-- Retained ordinary CSR read helpers preserve every state field. These helpers
-- are not reachable from the riscv-mi instruction AST.
example (s : riscv_state) : (CSRMap 256 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 257 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 320 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 321 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3394 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3395 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 512 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 513 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 576 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 577 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 578 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 579 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3840 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3841 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3856 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 768 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 769 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 832 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 833 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 834 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 835 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 896 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 897 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 898 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 899 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 900 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 901 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 1920 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 1921 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 1923 s).2 = s := by rfl

end Flapjack.Test.L3CSRDispatchParity
