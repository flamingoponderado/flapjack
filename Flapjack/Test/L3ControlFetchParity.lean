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

-- control_scsr_0
example (s : riscv_state) (v : SupervisorCSR) : «write'SCSR» v {s with procID := 0} =
 (let t := {s with procID := 0}; {t with c_SCSR := holUpdate 0 v t.c_SCSR}) := by rfl

-- control_mrts_0_0
example (s : riscv_state) : «dfn'MRTS» {s with procID := 0, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 0, mepc := 0}} =
 (let t := {s with procID := 0, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 0, mepc := 0}}; {t with c_SCSR := holUpdate 0 {t.c_SCSR 0 with scause := (t.c_MCSR 0).mcause, sbadaddr := 0, sepc := 0} t.c_SCSR, c_MCSR := holUpdate 0 {t.c_MCSR 0 with mstatus := {(t.c_MCSR 0).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 0 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

-- control_mrts_0_1
example (s : riscv_state) : «dfn'MRTS» {s with procID := 0, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 1, mepc := 4095}} =
 (let t := {s with procID := 0, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 1, mepc := 4095}}; {t with c_SCSR := holUpdate 0 {t.c_SCSR 0 with scause := (t.c_MCSR 0).mcause, sbadaddr := 1, sepc := 4095} t.c_SCSR, c_MCSR := holUpdate 0 {t.c_MCSR 0 with mstatus := {(t.c_MCSR 0).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 0 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

-- control_mrts_0_2
example (s : riscv_state) : «dfn'MRTS» {s with procID := 0, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 9223372036854775808, mepc := 18446744073709551615}} =
 (let t := {s with procID := 0, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 9223372036854775808, mepc := 18446744073709551615}}; {t with c_SCSR := holUpdate 0 {t.c_SCSR 0 with scause := (t.c_MCSR 0).mcause, sbadaddr := 9223372036854775808, sepc := 18446744073709551615} t.c_SCSR, c_MCSR := holUpdate 0 {t.c_MCSR 0 with mstatus := {(t.c_MCSR 0).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 0 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

-- control_mrts_0_3
example (s : riscv_state) : «dfn'MRTS» {s with procID := 0, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 18446744073709551615, mepc := 9223372036854775808}} =
 (let t := {s with procID := 0, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 18446744073709551615, mepc := 9223372036854775808}}; {t with c_SCSR := holUpdate 0 {t.c_SCSR 0 with scause := (t.c_MCSR 0).mcause, sbadaddr := 18446744073709551615, sepc := 9223372036854775808} t.c_SCSR, c_MCSR := holUpdate 0 {t.c_MCSR 0 with mstatus := {(t.c_MCSR 0).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 0 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

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

-- control_scsr_7
example (s : riscv_state) (v : SupervisorCSR) : «write'SCSR» v {s with procID := 7} =
 (let t := {s with procID := 7}; {t with c_SCSR := holUpdate 7 v t.c_SCSR}) := by rfl

-- control_mrts_7_0
example (s : riscv_state) : «dfn'MRTS» {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 0, mepc := 0}} =
 (let t := {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 0, mepc := 0}}; {t with c_SCSR := holUpdate 7 {t.c_SCSR 7 with scause := (t.c_MCSR 7).mcause, sbadaddr := 0, sepc := 0} t.c_SCSR, c_MCSR := holUpdate 7 {t.c_MCSR 7 with mstatus := {(t.c_MCSR 7).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 7 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

-- control_mrts_7_1
example (s : riscv_state) : «dfn'MRTS» {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 1, mepc := 4095}} =
 (let t := {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 1, mepc := 4095}}; {t with c_SCSR := holUpdate 7 {t.c_SCSR 7 with scause := (t.c_MCSR 7).mcause, sbadaddr := 1, sepc := 4095} t.c_SCSR, c_MCSR := holUpdate 7 {t.c_MCSR 7 with mstatus := {(t.c_MCSR 7).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 7 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

-- control_mrts_7_2
example (s : riscv_state) : «dfn'MRTS» {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 9223372036854775808, mepc := 18446744073709551615}} =
 (let t := {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 9223372036854775808, mepc := 18446744073709551615}}; {t with c_SCSR := holUpdate 7 {t.c_SCSR 7 with scause := (t.c_MCSR 7).mcause, sbadaddr := 9223372036854775808, sepc := 18446744073709551615} t.c_SCSR, c_MCSR := holUpdate 7 {t.c_MCSR 7 with mstatus := {(t.c_MCSR 7).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 7 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

-- control_mrts_7_3
example (s : riscv_state) : «dfn'MRTS» {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 18446744073709551615, mepc := 9223372036854775808}} =
 (let t := {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 18446744073709551615, mepc := 9223372036854775808}}; {t with c_SCSR := holUpdate 7 {t.c_SCSR 7 with scause := (t.c_MCSR 7).mcause, sbadaddr := 18446744073709551615, sepc := 9223372036854775808} t.c_SCSR, c_MCSR := holUpdate 7 {t.c_MCSR 7 with mstatus := {(t.c_MCSR 7).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 7 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

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

-- control_scsr_255
example (s : riscv_state) (v : SupervisorCSR) : «write'SCSR» v {s with procID := 255} =
 (let t := {s with procID := 255}; {t with c_SCSR := holUpdate 255 v t.c_SCSR}) := by rfl

-- control_mrts_255_0
example (s : riscv_state) : «dfn'MRTS» {s with procID := 255, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 0, mepc := 0}} =
 (let t := {s with procID := 255, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 0, mepc := 0}}; {t with c_SCSR := holUpdate 255 {t.c_SCSR 255 with scause := (t.c_MCSR 255).mcause, sbadaddr := 0, sepc := 0} t.c_SCSR, c_MCSR := holUpdate 255 {t.c_MCSR 255 with mstatus := {(t.c_MCSR 255).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 255 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

-- control_mrts_255_1
example (s : riscv_state) : «dfn'MRTS» {s with procID := 255, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 1, mepc := 4095}} =
 (let t := {s with procID := 255, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 1, mepc := 4095}}; {t with c_SCSR := holUpdate 255 {t.c_SCSR 255 with scause := (t.c_MCSR 255).mcause, sbadaddr := 1, sepc := 4095} t.c_SCSR, c_MCSR := holUpdate 255 {t.c_MCSR 255 with mstatus := {(t.c_MCSR 255).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 255 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

-- control_mrts_255_2
example (s : riscv_state) : «dfn'MRTS» {s with procID := 255, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 9223372036854775808, mepc := 18446744073709551615}} =
 (let t := {s with procID := 255, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 9223372036854775808, mepc := 18446744073709551615}}; {t with c_SCSR := holUpdate 255 {t.c_SCSR 255 with scause := (t.c_MCSR 255).mcause, sbadaddr := 9223372036854775808, sepc := 18446744073709551615} t.c_SCSR, c_MCSR := holUpdate 255 {t.c_MCSR 255 with mstatus := {(t.c_MCSR 255).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 255 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

-- control_mrts_255_3
example (s : riscv_state) : «dfn'MRTS» {s with procID := 255, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 18446744073709551615, mepc := 9223372036854775808}} =
 (let t := {s with procID := 255, c_MCSR := fun id => {s.c_MCSR id with mbadaddr := 18446744073709551615, mepc := 9223372036854775808}}; {t with c_SCSR := holUpdate 255 {t.c_SCSR 255 with scause := (t.c_MCSR 255).mcause, sbadaddr := 18446744073709551615, sepc := 9223372036854775808} t.c_SCSR, c_MCSR := holUpdate 255 {t.c_MCSR 255 with mstatus := {(t.c_MCSR 255).mstatus with MPRV := 1}} t.c_MCSR, c_NextFetch := holUpdate 255 (some TransferControl.Mrts) t.c_NextFetch}) := by
  simp [«dfn'MRTS», «write'SCSR», SCSR, MCSR, «write'MCSR», «write'NextFetch», holUpdate, privLevel, updateOverwrite]

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
