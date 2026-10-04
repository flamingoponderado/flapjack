import Flapjack.RiscV.L3.Defs.ControlFetch

namespace Flapjack.Test.L3ControlFetchParity
open Flapjack.RiscV.L3

/-- Flapjack-specific fixture normalization of repeated canonical function writes. -/
private theorem updateOverwrite {α β : Type} [DecidableEq α]
    (a : α) (b c : β) (f : α → β) :
    holUpdate a b (holUpdate a c f) = holUpdate a b f := by
  funext x
  simp only [holUpdate]
  split <;> rfl

-- control_FETCH_MISALIGNED_0_0
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 0 {s with procID := 0} =
 (let t := {s with procID := 0}; {t with c_NextFetch := holUpdate 0 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 0})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_0_1
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 1 {s with procID := 0} =
 (let t := {s with procID := 0}; {t with c_NextFetch := holUpdate 0 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 1})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_0_2
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 9223372036854775808 {s with procID := 0} =
 (let t := {s with procID := 0}; {t with c_NextFetch := holUpdate 0 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 9223372036854775808})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_0_3
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 18446744073709551615 {s with procID := 0} =
 (let t := {s with procID := 0}; {t with c_NextFetch := holUpdate 0 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 18446744073709551615})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_0_0
example (s : riscv_state) : «dfn'FETCH_FAULT» 0 {s with procID := 0} =
 (let t := {s with procID := 0}; {t with c_NextFetch := holUpdate 0 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 0})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_0_1
example (s : riscv_state) : «dfn'FETCH_FAULT» 1 {s with procID := 0} =
 (let t := {s with procID := 0}; {t with c_NextFetch := holUpdate 0 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 1})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_0_2
example (s : riscv_state) : «dfn'FETCH_FAULT» 9223372036854775808 {s with procID := 0} =
 (let t := {s with procID := 0}; {t with c_NextFetch := holUpdate 0 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 9223372036854775808})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_0_3
example (s : riscv_state) : «dfn'FETCH_FAULT» 18446744073709551615 {s with procID := 0} =
 (let t := {s with procID := 0}; {t with c_NextFetch := holUpdate 0 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 18446744073709551615})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_7_0
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 0 {s with procID := 7} =
 (let t := {s with procID := 7}; {t with c_NextFetch := holUpdate 7 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 0})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_7_1
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 1 {s with procID := 7} =
 (let t := {s with procID := 7}; {t with c_NextFetch := holUpdate 7 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 1})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_7_2
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 9223372036854775808 {s with procID := 7} =
 (let t := {s with procID := 7}; {t with c_NextFetch := holUpdate 7 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 9223372036854775808})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_7_3
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 18446744073709551615 {s with procID := 7} =
 (let t := {s with procID := 7}; {t with c_NextFetch := holUpdate 7 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 18446744073709551615})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_7_0
example (s : riscv_state) : «dfn'FETCH_FAULT» 0 {s with procID := 7} =
 (let t := {s with procID := 7}; {t with c_NextFetch := holUpdate 7 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 0})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_7_1
example (s : riscv_state) : «dfn'FETCH_FAULT» 1 {s with procID := 7} =
 (let t := {s with procID := 7}; {t with c_NextFetch := holUpdate 7 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 1})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_7_2
example (s : riscv_state) : «dfn'FETCH_FAULT» 9223372036854775808 {s with procID := 7} =
 (let t := {s with procID := 7}; {t with c_NextFetch := holUpdate 7 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 9223372036854775808})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_7_3
example (s : riscv_state) : «dfn'FETCH_FAULT» 18446744073709551615 {s with procID := 7} =
 (let t := {s with procID := 7}; {t with c_NextFetch := holUpdate 7 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 18446744073709551615})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_255_0
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 0 {s with procID := 255} =
 (let t := {s with procID := 255}; {t with c_NextFetch := holUpdate 255 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 0})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_255_1
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 1 {s with procID := 255} =
 (let t := {s with procID := 255}; {t with c_NextFetch := holUpdate 255 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 1})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_255_2
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 9223372036854775808 {s with procID := 255} =
 (let t := {s with procID := 255}; {t with c_NextFetch := holUpdate 255 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 9223372036854775808})) t.c_NextFetch}) := by rfl

-- control_FETCH_MISALIGNED_255_3
example (s : riscv_state) : «dfn'FETCH_MISALIGNED» 18446744073709551615 {s with procID := 255} =
 (let t := {s with procID := 255}; {t with c_NextFetch := holUpdate 255 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Misaligned, badaddr := some 18446744073709551615})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_255_0
example (s : riscv_state) : «dfn'FETCH_FAULT» 0 {s with procID := 255} =
 (let t := {s with procID := 255}; {t with c_NextFetch := holUpdate 255 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 0})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_255_1
example (s : riscv_state) : «dfn'FETCH_FAULT» 1 {s with procID := 255} =
 (let t := {s with procID := 255}; {t with c_NextFetch := holUpdate 255 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 1})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_255_2
example (s : riscv_state) : «dfn'FETCH_FAULT» 9223372036854775808 {s with procID := 255} =
 (let t := {s with procID := 255}; {t with c_NextFetch := holUpdate 255 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 9223372036854775808})) t.c_NextFetch}) := by rfl

-- control_FETCH_FAULT_255_3
example (s : riscv_state) : «dfn'FETCH_FAULT» 18446744073709551615 {s with procID := 255} =
 (let t := {s with procID := 255}; {t with c_NextFetch := holUpdate 255 (some (TransferControl.Trap {trap := ExceptionType.Fetch_Fault, badaddr := some 18446744073709551615})) t.c_NextFetch}) := by rfl

end Flapjack.Test.L3ControlFetchParity
