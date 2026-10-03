import Flapjack.RiscV.L3.Defs.FPMemory

namespace Flapjack.Test.L3FPMemoryParity
open Flapjack.RiscV.L3
/-! Flapjack-specific full-state regression fixtures; not an equivalence theorem.
Numeric expected addresses/payloads are independently calculated. Whole-state
routes use reviewed raw memory/FPR writers, including all their frame effects.
The production definitions retain arbitrary translation results and states. -/
private def fixture (s : riscv_state) (base payload : BitVec 64)
    (byte : BitVec 8) (vm : BitVec 5) (core : BitVec 8) : riscv_state :=
 {s with procID := core, c_gpr := (fun _ _ => base), c_fpr := (fun _ _ => payload), MEM8 := (fun _ => byte), c_MCSR := (fun id => {s.c_MCSR id with mstatus := {(s.c_MCSR id).mstatus with MMPRV := false, MPRV := 0, VM := vm}})}

attribute [local irreducible] rawWriteData «write'FPRS» «write'FPRD»

-- fp_memory_FLW_0_0_0
example (s : riscv_state) : «dfn'FLW» (0,1,0) (fixture s 0 0 0 0 7) =
 «write'FPRS» (0,0) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_0_1
example (s : riscv_state) : «dfn'FLW» (1,1,0) (fixture s 0 0 0 0 7) =
 «write'FPRS» (0,1) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_0_2
example (s : riscv_state) : «dfn'FLW» (2,1,0) (fixture s 0 0 0 0 7) =
 «write'FPRS» (0,2) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_0_7
example (s : riscv_state) : «dfn'FLW» (7,1,0) (fixture s 0 0 0 0 7) =
 «write'FPRS» (0,7) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_1_0
example (s : riscv_state) : «dfn'FLW» (0,1,4095) (fixture s 1 1311768467177459183 171 0 255) =
 «write'FPRS» (2880154539,0) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_1_1
example (s : riscv_state) : «dfn'FLW» (1,1,4095) (fixture s 1 1311768467177459183 171 0 255) =
 «write'FPRS» (2880154539,1) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_1_2
example (s : riscv_state) : «dfn'FLW» (2,1,4095) (fixture s 1 1311768467177459183 171 0 255) =
 «write'FPRS» (2880154539,2) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_1_7
example (s : riscv_state) : «dfn'FLW» (7,1,4095) (fixture s 1 1311768467177459183 171 0 255) =
 «write'FPRS» (2880154539,7) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_2_0
example (s : riscv_state) : «dfn'FLW» (0,1,2048) (fixture s 0 9223372036854775809 128 0 7) =
 «write'FPRS» (2155905152,0) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_2_1
example (s : riscv_state) : «dfn'FLW» (1,1,2048) (fixture s 0 9223372036854775809 128 0 7) =
 «write'FPRS» (2155905152,1) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_2_2
example (s : riscv_state) : «dfn'FLW» (2,1,2048) (fixture s 0 9223372036854775809 128 0 7) =
 «write'FPRS» (2155905152,2) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_2_7
example (s : riscv_state) : «dfn'FLW» (7,1,2048) (fixture s 0 9223372036854775809 128 0 7) =
 «write'FPRS» (2155905152,7) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_3_0
example (s : riscv_state) : «dfn'FLW» (0,1,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 «write'FPRS» (4294967295,0) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_3_1
example (s : riscv_state) : «dfn'FLW» (1,1,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 «write'FPRS» (4294967295,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_3_2
example (s : riscv_state) : «dfn'FLW» (2,1,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 «write'FPRS» (4294967295,2) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_3_7
example (s : riscv_state) : «dfn'FLW» (7,1,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 «write'FPRS» (4294967295,7) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_4_0
example (s : riscv_state) : «dfn'FLW» (0,1,2047) (fixture s 8 9218868437227405313 171 0 7) =
 «write'FPRS» (2880154539,0) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_4_1
example (s : riscv_state) : «dfn'FLW» (1,1,2047) (fixture s 8 9218868437227405313 171 0 7) =
 «write'FPRS» (2880154539,1) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_4_2
example (s : riscv_state) : «dfn'FLW» (2,1,2047) (fixture s 8 9218868437227405313 171 0 7) =
 «write'FPRS» (2880154539,2) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_4_7
example (s : riscv_state) : «dfn'FLW» (7,1,2047) (fixture s 8 9218868437227405313 171 0 7) =
 «write'FPRS» (2880154539,7) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_5_0
example (s : riscv_state) : «dfn'FLW» (0,1,0) (fixture s 7 2147483648 128 0 255) =
 «write'FPRS» (2155905152,0) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_5_1
example (s : riscv_state) : «dfn'FLW» (1,1,0) (fixture s 7 2147483648 128 0 255) =
 «write'FPRS» (2155905152,1) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_5_2
example (s : riscv_state) : «dfn'FLW» (2,1,0) (fixture s 7 2147483648 128 0 255) =
 «write'FPRS» (2155905152,2) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_5_7
example (s : riscv_state) : «dfn'FLW» (7,1,0) (fixture s 7 2147483648 128 0 255) =
 «write'FPRS» (2155905152,7) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_6_0
example (s : riscv_state) : «dfn'FLW» (0,0,4095) (fixture s 123 0 255 0 7) =
 «write'FPRS» (4294967295,0) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FLW», fixture, GPR, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_6_1
example (s : riscv_state) : «dfn'FLW» (1,0,4095) (fixture s 123 0 255 0 7) =
 «write'FPRS» (4294967295,1) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FLW», fixture, GPR, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_6_2
example (s : riscv_state) : «dfn'FLW» (2,0,4095) (fixture s 123 0 255 0 7) =
 «write'FPRS» (4294967295,2) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FLW», fixture, GPR, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_6_7
example (s : riscv_state) : «dfn'FLW» (7,0,4095) (fixture s 123 0 255 0 7) =
 «write'FPRS» (4294967295,7) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FLW», fixture, GPR, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_7_0
example (s : riscv_state) : «dfn'FLW» (0,1,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 «write'FPRS» (0,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_7_1
example (s : riscv_state) : «dfn'FLW» (1,1,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 «write'FPRS» (0,1) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_7_2
example (s : riscv_state) : «dfn'FLW» (2,1,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 «write'FPRS» (0,2) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_0_7_7
example (s : riscv_state) : «dfn'FLW» (7,1,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 «write'FPRS» (0,7) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLW_1_0_0
example (s : riscv_state) : «dfn'FLW» (0,1,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_0_1
example (s : riscv_state) : «dfn'FLW» (1,1,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_0_2
example (s : riscv_state) : «dfn'FLW» (2,1,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_0_7
example (s : riscv_state) : «dfn'FLW» (7,1,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_1_0
example (s : riscv_state) : «dfn'FLW» (0,1,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_1_1
example (s : riscv_state) : «dfn'FLW» (1,1,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_1_2
example (s : riscv_state) : «dfn'FLW» (2,1,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_1_7
example (s : riscv_state) : «dfn'FLW» (7,1,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_2_0
example (s : riscv_state) : «dfn'FLW» (0,1,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_2_1
example (s : riscv_state) : «dfn'FLW» (1,1,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_2_2
example (s : riscv_state) : «dfn'FLW» (2,1,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_2_7
example (s : riscv_state) : «dfn'FLW» (7,1,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_3_0
example (s : riscv_state) : «dfn'FLW» (0,1,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_3_1
example (s : riscv_state) : «dfn'FLW» (1,1,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_3_2
example (s : riscv_state) : «dfn'FLW» (2,1,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_3_7
example (s : riscv_state) : «dfn'FLW» (7,1,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_4_0
example (s : riscv_state) : «dfn'FLW» (0,1,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Load_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_4_1
example (s : riscv_state) : «dfn'FLW» (1,1,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Load_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_4_2
example (s : riscv_state) : «dfn'FLW» (2,1,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Load_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_4_7
example (s : riscv_state) : «dfn'FLW» (7,1,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Load_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_5_0
example (s : riscv_state) : «dfn'FLW» (0,1,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Load_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_5_1
example (s : riscv_state) : «dfn'FLW» (1,1,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Load_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_5_2
example (s : riscv_state) : «dfn'FLW» (2,1,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Load_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_5_7
example (s : riscv_state) : «dfn'FLW» (7,1,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Load_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_6_0
example (s : riscv_state) : «dfn'FLW» (0,0,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FLW», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_6_1
example (s : riscv_state) : «dfn'FLW» (1,0,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FLW», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_6_2
example (s : riscv_state) : «dfn'FLW» (2,0,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FLW», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_6_7
example (s : riscv_state) : «dfn'FLW» (7,0,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FLW», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_7_0
example (s : riscv_state) : «dfn'FLW» (0,1,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Load_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_7_1
example (s : riscv_state) : «dfn'FLW» (1,1,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Load_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_7_2
example (s : riscv_state) : «dfn'FLW» (2,1,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Load_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLW_1_7_7
example (s : riscv_state) : «dfn'FLW» (7,1,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Load_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FLW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_0_0_0
example (s : riscv_state) : «dfn'FLD» (0,1,0) (fixture s 0 0 0 0 7) =
 «write'FPRD» (0,0) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_0_1
example (s : riscv_state) : «dfn'FLD» (1,1,0) (fixture s 0 0 0 0 7) =
 «write'FPRD» (0,1) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_0_2
example (s : riscv_state) : «dfn'FLD» (2,1,0) (fixture s 0 0 0 0 7) =
 «write'FPRD» (0,2) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_0_7
example (s : riscv_state) : «dfn'FLD» (7,1,0) (fixture s 0 0 0 0 7) =
 «write'FPRD» (0,7) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_1_0
example (s : riscv_state) : «dfn'FLD» (0,1,4095) (fixture s 1 1311768467177459183 171 0 255) =
 «write'FPRD» (12370169555311111083,0) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_1_1
example (s : riscv_state) : «dfn'FLD» (1,1,4095) (fixture s 1 1311768467177459183 171 0 255) =
 «write'FPRD» (12370169555311111083,1) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_1_2
example (s : riscv_state) : «dfn'FLD» (2,1,4095) (fixture s 1 1311768467177459183 171 0 255) =
 «write'FPRD» (12370169555311111083,2) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_1_7
example (s : riscv_state) : «dfn'FLD» (7,1,4095) (fixture s 1 1311768467177459183 171 0 255) =
 «write'FPRD» (12370169555311111083,7) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_2_0
example (s : riscv_state) : «dfn'FLD» (0,1,2048) (fixture s 0 9223372036854775809 128 0 7) =
 «write'FPRD» (9259542123273814144,0) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_2_1
example (s : riscv_state) : «dfn'FLD» (1,1,2048) (fixture s 0 9223372036854775809 128 0 7) =
 «write'FPRD» (9259542123273814144,1) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_2_2
example (s : riscv_state) : «dfn'FLD» (2,1,2048) (fixture s 0 9223372036854775809 128 0 7) =
 «write'FPRD» (9259542123273814144,2) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_2_7
example (s : riscv_state) : «dfn'FLD» (7,1,2048) (fixture s 0 9223372036854775809 128 0 7) =
 «write'FPRD» (9259542123273814144,7) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_3_0
example (s : riscv_state) : «dfn'FLD» (0,1,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 «write'FPRD» (18446744073709551615,0) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_3_1
example (s : riscv_state) : «dfn'FLD» (1,1,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 «write'FPRD» (18446744073709551615,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_3_2
example (s : riscv_state) : «dfn'FLD» (2,1,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 «write'FPRD» (18446744073709551615,2) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_3_7
example (s : riscv_state) : «dfn'FLD» (7,1,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 «write'FPRD» (18446744073709551615,7) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_4_0
example (s : riscv_state) : «dfn'FLD» (0,1,2047) (fixture s 8 9218868437227405313 171 0 7) =
 «write'FPRD» (12370169555311111083,0) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_4_1
example (s : riscv_state) : «dfn'FLD» (1,1,2047) (fixture s 8 9218868437227405313 171 0 7) =
 «write'FPRD» (12370169555311111083,1) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_4_2
example (s : riscv_state) : «dfn'FLD» (2,1,2047) (fixture s 8 9218868437227405313 171 0 7) =
 «write'FPRD» (12370169555311111083,2) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_4_7
example (s : riscv_state) : «dfn'FLD» (7,1,2047) (fixture s 8 9218868437227405313 171 0 7) =
 «write'FPRD» (12370169555311111083,7) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_5_0
example (s : riscv_state) : «dfn'FLD» (0,1,0) (fixture s 7 2147483648 128 0 255) =
 «write'FPRD» (9259542123273814144,0) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_5_1
example (s : riscv_state) : «dfn'FLD» (1,1,0) (fixture s 7 2147483648 128 0 255) =
 «write'FPRD» (9259542123273814144,1) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_5_2
example (s : riscv_state) : «dfn'FLD» (2,1,0) (fixture s 7 2147483648 128 0 255) =
 «write'FPRD» (9259542123273814144,2) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_5_7
example (s : riscv_state) : «dfn'FLD» (7,1,0) (fixture s 7 2147483648 128 0 255) =
 «write'FPRD» (9259542123273814144,7) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_6_0
example (s : riscv_state) : «dfn'FLD» (0,0,4095) (fixture s 123 0 255 0 7) =
 «write'FPRD» (18446744073709551615,0) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FLD», fixture, GPR, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_6_1
example (s : riscv_state) : «dfn'FLD» (1,0,4095) (fixture s 123 0 255 0 7) =
 «write'FPRD» (18446744073709551615,1) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FLD», fixture, GPR, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_6_2
example (s : riscv_state) : «dfn'FLD» (2,0,4095) (fixture s 123 0 255 0 7) =
 «write'FPRD» (18446744073709551615,2) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FLD», fixture, GPR, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_6_7
example (s : riscv_state) : «dfn'FLD» (7,0,4095) (fixture s 123 0 255 0 7) =
 «write'FPRD» (18446744073709551615,7) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FLD», fixture, GPR, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_7_0
example (s : riscv_state) : «dfn'FLD» (0,1,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 «write'FPRD» (0,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_7_1
example (s : riscv_state) : «dfn'FLD» (1,1,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 «write'FPRD» (0,1) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_7_2
example (s : riscv_state) : «dfn'FLD» (2,1,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 «write'FPRD» (0,2) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_0_7_7
example (s : riscv_state) : «dfn'FLD» (7,1,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 «write'FPRD» (0,7) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, vmType, rawReadData, MEM, holWordExtract]

-- fp_memory_FLD_1_0_0
example (s : riscv_state) : «dfn'FLD» (0,1,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_0_1
example (s : riscv_state) : «dfn'FLD» (1,1,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_0_2
example (s : riscv_state) : «dfn'FLD» (2,1,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_0_7
example (s : riscv_state) : «dfn'FLD» (7,1,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_1_0
example (s : riscv_state) : «dfn'FLD» (0,1,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_1_1
example (s : riscv_state) : «dfn'FLD» (1,1,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_1_2
example (s : riscv_state) : «dfn'FLD» (2,1,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_1_7
example (s : riscv_state) : «dfn'FLD» (7,1,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_2_0
example (s : riscv_state) : «dfn'FLD» (0,1,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_2_1
example (s : riscv_state) : «dfn'FLD» (1,1,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_2_2
example (s : riscv_state) : «dfn'FLD» (2,1,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_2_7
example (s : riscv_state) : «dfn'FLD» (7,1,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_3_0
example (s : riscv_state) : «dfn'FLD» (0,1,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_3_1
example (s : riscv_state) : «dfn'FLD» (1,1,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_3_2
example (s : riscv_state) : «dfn'FLD» (2,1,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_3_7
example (s : riscv_state) : «dfn'FLD» (7,1,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Load_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_4_0
example (s : riscv_state) : «dfn'FLD» (0,1,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Load_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_4_1
example (s : riscv_state) : «dfn'FLD» (1,1,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Load_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_4_2
example (s : riscv_state) : «dfn'FLD» (2,1,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Load_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_4_7
example (s : riscv_state) : «dfn'FLD» (7,1,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Load_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_5_0
example (s : riscv_state) : «dfn'FLD» (0,1,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Load_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_5_1
example (s : riscv_state) : «dfn'FLD» (1,1,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Load_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_5_2
example (s : riscv_state) : «dfn'FLD» (2,1,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Load_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_5_7
example (s : riscv_state) : «dfn'FLD» (7,1,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Load_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_6_0
example (s : riscv_state) : «dfn'FLD» (0,0,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FLD», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_6_1
example (s : riscv_state) : «dfn'FLD» (1,0,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FLD», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_6_2
example (s : riscv_state) : «dfn'FLD» (2,0,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FLD», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_6_7
example (s : riscv_state) : «dfn'FLD» (7,0,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Load_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FLD», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_7_0
example (s : riscv_state) : «dfn'FLD» (0,1,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Load_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_7_1
example (s : riscv_state) : «dfn'FLD» (1,1,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Load_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_7_2
example (s : riscv_state) : «dfn'FLD» (2,1,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Load_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FLD_1_7_7
example (s : riscv_state) : «dfn'FLD» (7,1,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Load_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FLD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_0_0_0
example (s : riscv_state) : «dfn'FSW» (1,0,0) (fixture s 0 0 0 0 7) =
 rawWriteData (0,0,4) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_0_1
example (s : riscv_state) : «dfn'FSW» (1,1,0) (fixture s 0 0 0 0 7) =
 rawWriteData (0,0,4) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_0_2
example (s : riscv_state) : «dfn'FSW» (1,2,0) (fixture s 0 0 0 0 7) =
 rawWriteData (0,0,4) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_0_7
example (s : riscv_state) : «dfn'FSW» (1,7,0) (fixture s 0 0 0 0 7) =
 rawWriteData (0,0,4) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_1_0
example (s : riscv_state) : «dfn'FSW» (1,0,4095) (fixture s 1 1311768467177459183 171 0 255) =
 rawWriteData (0,2309737967,4) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_1_1
example (s : riscv_state) : «dfn'FSW» (1,1,4095) (fixture s 1 1311768467177459183 171 0 255) =
 rawWriteData (0,2309737967,4) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_1_2
example (s : riscv_state) : «dfn'FSW» (1,2,4095) (fixture s 1 1311768467177459183 171 0 255) =
 rawWriteData (0,2309737967,4) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_1_7
example (s : riscv_state) : «dfn'FSW» (1,7,4095) (fixture s 1 1311768467177459183 171 0 255) =
 rawWriteData (0,2309737967,4) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_2_0
example (s : riscv_state) : «dfn'FSW» (1,0,2048) (fixture s 0 9223372036854775809 128 0 7) =
 rawWriteData (18446744073709549568,1,4) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_2_1
example (s : riscv_state) : «dfn'FSW» (1,1,2048) (fixture s 0 9223372036854775809 128 0 7) =
 rawWriteData (18446744073709549568,1,4) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_2_2
example (s : riscv_state) : «dfn'FSW» (1,2,2048) (fixture s 0 9223372036854775809 128 0 7) =
 rawWriteData (18446744073709549568,1,4) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_2_7
example (s : riscv_state) : «dfn'FSW» (1,7,2048) (fixture s 0 9223372036854775809 128 0 7) =
 rawWriteData (18446744073709549568,1,4) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_3_0
example (s : riscv_state) : «dfn'FSW» (1,0,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 rawWriteData (0,4294967295,4) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_3_1
example (s : riscv_state) : «dfn'FSW» (1,1,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 rawWriteData (0,4294967295,4) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_3_2
example (s : riscv_state) : «dfn'FSW» (1,2,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 rawWriteData (0,4294967295,4) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_3_7
example (s : riscv_state) : «dfn'FSW» (1,7,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 rawWriteData (0,4294967295,4) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_4_0
example (s : riscv_state) : «dfn'FSW» (1,0,2047) (fixture s 8 9218868437227405313 171 0 7) =
 rawWriteData (2055,1,4) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_4_1
example (s : riscv_state) : «dfn'FSW» (1,1,2047) (fixture s 8 9218868437227405313 171 0 7) =
 rawWriteData (2055,1,4) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_4_2
example (s : riscv_state) : «dfn'FSW» (1,2,2047) (fixture s 8 9218868437227405313 171 0 7) =
 rawWriteData (2055,1,4) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_4_7
example (s : riscv_state) : «dfn'FSW» (1,7,2047) (fixture s 8 9218868437227405313 171 0 7) =
 rawWriteData (2055,1,4) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_5_0
example (s : riscv_state) : «dfn'FSW» (1,0,0) (fixture s 7 2147483648 128 0 255) =
 rawWriteData (7,2147483648,4) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_5_1
example (s : riscv_state) : «dfn'FSW» (1,1,0) (fixture s 7 2147483648 128 0 255) =
 rawWriteData (7,2147483648,4) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_5_2
example (s : riscv_state) : «dfn'FSW» (1,2,0) (fixture s 7 2147483648 128 0 255) =
 rawWriteData (7,2147483648,4) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_5_7
example (s : riscv_state) : «dfn'FSW» (1,7,0) (fixture s 7 2147483648 128 0 255) =
 rawWriteData (7,2147483648,4) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_6_0
example (s : riscv_state) : «dfn'FSW» (0,0,4095) (fixture s 123 0 255 0 7) =
 rawWriteData (18446744073709551615,0,4) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FSW», fixture, GPR, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_6_1
example (s : riscv_state) : «dfn'FSW» (0,1,4095) (fixture s 123 0 255 0 7) =
 rawWriteData (18446744073709551615,0,4) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FSW», fixture, GPR, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_6_2
example (s : riscv_state) : «dfn'FSW» (0,2,4095) (fixture s 123 0 255 0 7) =
 rawWriteData (18446744073709551615,0,4) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FSW», fixture, GPR, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_6_7
example (s : riscv_state) : «dfn'FSW» (0,7,4095) (fixture s 123 0 255 0 7) =
 rawWriteData (18446744073709551615,0,4) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FSW», fixture, GPR, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_7_0
example (s : riscv_state) : «dfn'FSW» (1,0,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 rawWriteData (9223372036854775808,3405691582,4) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_7_1
example (s : riscv_state) : «dfn'FSW» (1,1,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 rawWriteData (9223372036854775808,3405691582,4) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_7_2
example (s : riscv_state) : «dfn'FSW» (1,2,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 rawWriteData (9223372036854775808,3405691582,4) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_0_7_7
example (s : riscv_state) : «dfn'FSW» (1,7,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 rawWriteData (9223372036854775808,3405691582,4) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRS, fpr, holWordExtract]

-- fp_memory_FSW_1_0_0
example (s : riscv_state) : «dfn'FSW» (1,0,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_0_1
example (s : riscv_state) : «dfn'FSW» (1,1,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_0_2
example (s : riscv_state) : «dfn'FSW» (1,2,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_0_7
example (s : riscv_state) : «dfn'FSW» (1,7,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_1_0
example (s : riscv_state) : «dfn'FSW» (1,0,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_1_1
example (s : riscv_state) : «dfn'FSW» (1,1,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_1_2
example (s : riscv_state) : «dfn'FSW» (1,2,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_1_7
example (s : riscv_state) : «dfn'FSW» (1,7,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_2_0
example (s : riscv_state) : «dfn'FSW» (1,0,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_2_1
example (s : riscv_state) : «dfn'FSW» (1,1,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_2_2
example (s : riscv_state) : «dfn'FSW» (1,2,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_2_7
example (s : riscv_state) : «dfn'FSW» (1,7,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_3_0
example (s : riscv_state) : «dfn'FSW» (1,0,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_3_1
example (s : riscv_state) : «dfn'FSW» (1,1,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_3_2
example (s : riscv_state) : «dfn'FSW» (1,2,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_3_7
example (s : riscv_state) : «dfn'FSW» (1,7,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_4_0
example (s : riscv_state) : «dfn'FSW» (1,0,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_4_1
example (s : riscv_state) : «dfn'FSW» (1,1,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_4_2
example (s : riscv_state) : «dfn'FSW» (1,2,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_4_7
example (s : riscv_state) : «dfn'FSW» (1,7,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_5_0
example (s : riscv_state) : «dfn'FSW» (1,0,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_5_1
example (s : riscv_state) : «dfn'FSW» (1,1,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_5_2
example (s : riscv_state) : «dfn'FSW» (1,2,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_5_7
example (s : riscv_state) : «dfn'FSW» (1,7,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_6_0
example (s : riscv_state) : «dfn'FSW» (0,0,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FSW», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_6_1
example (s : riscv_state) : «dfn'FSW» (0,1,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FSW», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_6_2
example (s : riscv_state) : «dfn'FSW» (0,2,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FSW», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_6_7
example (s : riscv_state) : «dfn'FSW» (0,7,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FSW», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_7_0
example (s : riscv_state) : «dfn'FSW» (1,0,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_7_1
example (s : riscv_state) : «dfn'FSW» (1,1,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_7_2
example (s : riscv_state) : «dfn'FSW» (1,2,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSW_1_7_7
example (s : riscv_state) : «dfn'FSW» (1,7,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FSW», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_0_0_0
example (s : riscv_state) : «dfn'FSD» (1,0,0) (fixture s 0 0 0 0 7) =
 rawWriteData (0,0,8) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_0_1
example (s : riscv_state) : «dfn'FSD» (1,1,0) (fixture s 0 0 0 0 7) =
 rawWriteData (0,0,8) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_0_2
example (s : riscv_state) : «dfn'FSD» (1,2,0) (fixture s 0 0 0 0 7) =
 rawWriteData (0,0,8) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_0_7
example (s : riscv_state) : «dfn'FSD» (1,7,0) (fixture s 0 0 0 0 7) =
 rawWriteData (0,0,8) (fixture s 0 0 0 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_1_0
example (s : riscv_state) : «dfn'FSD» (1,0,4095) (fixture s 1 1311768467177459183 171 0 255) =
 rawWriteData (0,1311768467177459183,8) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_1_1
example (s : riscv_state) : «dfn'FSD» (1,1,4095) (fixture s 1 1311768467177459183 171 0 255) =
 rawWriteData (0,1311768467177459183,8) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_1_2
example (s : riscv_state) : «dfn'FSD» (1,2,4095) (fixture s 1 1311768467177459183 171 0 255) =
 rawWriteData (0,1311768467177459183,8) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_1_7
example (s : riscv_state) : «dfn'FSD» (1,7,4095) (fixture s 1 1311768467177459183 171 0 255) =
 rawWriteData (0,1311768467177459183,8) (fixture s 1 1311768467177459183 171 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_2_0
example (s : riscv_state) : «dfn'FSD» (1,0,2048) (fixture s 0 9223372036854775809 128 0 7) =
 rawWriteData (18446744073709549568,9223372036854775809,8) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_2_1
example (s : riscv_state) : «dfn'FSD» (1,1,2048) (fixture s 0 9223372036854775809 128 0 7) =
 rawWriteData (18446744073709549568,9223372036854775809,8) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_2_2
example (s : riscv_state) : «dfn'FSD» (1,2,2048) (fixture s 0 9223372036854775809 128 0 7) =
 rawWriteData (18446744073709549568,9223372036854775809,8) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_2_7
example (s : riscv_state) : «dfn'FSD» (1,7,2048) (fixture s 0 9223372036854775809 128 0 7) =
 rawWriteData (18446744073709549568,9223372036854775809,8) (fixture s 0 9223372036854775809 128 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_3_0
example (s : riscv_state) : «dfn'FSD» (1,0,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 rawWriteData (0,18446744073709551615,8) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_3_1
example (s : riscv_state) : «dfn'FSD» (1,1,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 rawWriteData (0,18446744073709551615,8) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_3_2
example (s : riscv_state) : «dfn'FSD» (1,2,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 rawWriteData (0,18446744073709551615,8) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_3_7
example (s : riscv_state) : «dfn'FSD» (1,7,1) (fixture s 18446744073709551615 18446744073709551615 255 0 255) =
 rawWriteData (0,18446744073709551615,8) (fixture s 18446744073709551615 18446744073709551615 255 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_4_0
example (s : riscv_state) : «dfn'FSD» (1,0,2047) (fixture s 8 9218868437227405313 171 0 7) =
 rawWriteData (2055,9218868437227405313,8) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_4_1
example (s : riscv_state) : «dfn'FSD» (1,1,2047) (fixture s 8 9218868437227405313 171 0 7) =
 rawWriteData (2055,9218868437227405313,8) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_4_2
example (s : riscv_state) : «dfn'FSD» (1,2,2047) (fixture s 8 9218868437227405313 171 0 7) =
 rawWriteData (2055,9218868437227405313,8) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_4_7
example (s : riscv_state) : «dfn'FSD» (1,7,2047) (fixture s 8 9218868437227405313 171 0 7) =
 rawWriteData (2055,9218868437227405313,8) (fixture s 8 9218868437227405313 171 0 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_5_0
example (s : riscv_state) : «dfn'FSD» (1,0,0) (fixture s 7 2147483648 128 0 255) =
 rawWriteData (7,2147483648,8) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_5_1
example (s : riscv_state) : «dfn'FSD» (1,1,0) (fixture s 7 2147483648 128 0 255) =
 rawWriteData (7,2147483648,8) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_5_2
example (s : riscv_state) : «dfn'FSD» (1,2,0) (fixture s 7 2147483648 128 0 255) =
 rawWriteData (7,2147483648,8) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_5_7
example (s : riscv_state) : «dfn'FSD» (1,7,0) (fixture s 7 2147483648 128 0 255) =
 rawWriteData (7,2147483648,8) (fixture s 7 2147483648 128 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_6_0
example (s : riscv_state) : «dfn'FSD» (0,0,4095) (fixture s 123 0 255 0 7) =
 rawWriteData (18446744073709551615,0,8) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FSD», fixture, GPR, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_6_1
example (s : riscv_state) : «dfn'FSD» (0,1,4095) (fixture s 123 0 255 0 7) =
 rawWriteData (18446744073709551615,0,8) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FSD», fixture, GPR, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_6_2
example (s : riscv_state) : «dfn'FSD» (0,2,4095) (fixture s 123 0 255 0 7) =
 rawWriteData (18446744073709551615,0,8) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FSD», fixture, GPR, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_6_7
example (s : riscv_state) : «dfn'FSD» (0,7,4095) (fixture s 123 0 255 0 7) =
 rawWriteData (18446744073709551615,0,8) (fixture s 123 0 255 0 7) := by
  simp [«dfn'FSD», fixture, GPR, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_7_0
example (s : riscv_state) : «dfn'FSD» (1,0,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 rawWriteData (9223372036854775808,16045690984503098046,8) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_7_1
example (s : riscv_state) : «dfn'FSD» (1,1,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 rawWriteData (9223372036854775808,16045690984503098046,8) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_7_2
example (s : riscv_state) : «dfn'FSD» (1,2,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 rawWriteData (9223372036854775808,16045690984503098046,8) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_0_7_7
example (s : riscv_state) : «dfn'FSD» (1,7,0) (fixture s 9223372036854775808 16045690984503098046 0 0 255) =
 rawWriteData (9223372036854775808,16045690984503098046,8) (fixture s 9223372036854775808 16045690984503098046 0 0 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, vmType, FPRD, fpr]

-- fp_memory_FSD_1_0_0
example (s : riscv_state) : «dfn'FSD» (1,0,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_0_1
example (s : riscv_state) : «dfn'FSD» (1,1,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_0_2
example (s : riscv_state) : «dfn'FSD» (1,2,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_0_7
example (s : riscv_state) : «dfn'FSD» (1,7,0) (fixture s 0 0 0 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 0 0 0 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_1_0
example (s : riscv_state) : «dfn'FSD» (1,0,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_1_1
example (s : riscv_state) : «dfn'FSD» (1,1,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_1_2
example (s : riscv_state) : «dfn'FSD» (1,2,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_1_7
example (s : riscv_state) : «dfn'FSD» (1,7,4095) (fixture s 1 1311768467177459183 171 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 1 1311768467177459183 171 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_2_0
example (s : riscv_state) : «dfn'FSD» (1,0,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_2_1
example (s : riscv_state) : «dfn'FSD» (1,1,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_2_2
example (s : riscv_state) : «dfn'FSD» (1,2,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_2_7
example (s : riscv_state) : «dfn'FSD» (1,7,2048) (fixture s 0 9223372036854775809 128 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709549568) (fixture s 0 9223372036854775809 128 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_3_0
example (s : riscv_state) : «dfn'FSD» (1,0,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_3_1
example (s : riscv_state) : «dfn'FSD» (1,1,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_3_2
example (s : riscv_state) : «dfn'FSD» (1,2,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_3_7
example (s : riscv_state) : «dfn'FSD» (1,7,1) (fixture s 18446744073709551615 18446744073709551615 255 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,0) (fixture s 18446744073709551615 18446744073709551615 255 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_4_0
example (s : riscv_state) : «dfn'FSD» (1,0,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_4_1
example (s : riscv_state) : «dfn'FSD» (1,1,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_4_2
example (s : riscv_state) : «dfn'FSD» (1,2,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_4_7
example (s : riscv_state) : «dfn'FSD» (1,7,2047) (fixture s 8 9218868437227405313 171 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,2055) (fixture s 8 9218868437227405313 171 1 7) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_5_0
example (s : riscv_state) : «dfn'FSD» (1,0,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_5_1
example (s : riscv_state) : «dfn'FSD» (1,1,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_5_2
example (s : riscv_state) : «dfn'FSD» (1,2,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_5_7
example (s : riscv_state) : «dfn'FSD» (1,7,0) (fixture s 7 2147483648 128 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,7) (fixture s 7 2147483648 128 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_6_0
example (s : riscv_state) : «dfn'FSD» (0,0,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FSD», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_6_1
example (s : riscv_state) : «dfn'FSD» (0,1,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FSD», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_6_2
example (s : riscv_state) : «dfn'FSD» (0,2,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FSD», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_6_7
example (s : riscv_state) : «dfn'FSD» (0,7,4095) (fixture s 123 0 255 1 7) =
 signalAddressException (ExceptionType.Store_AMO_Fault,18446744073709551615) (fixture s 123 0 255 1 7) := by
  simp [«dfn'FSD», fixture, GPR, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_7_0
example (s : riscv_state) : «dfn'FSD» (1,0,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_7_1
example (s : riscv_state) : «dfn'FSD» (1,1,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_7_2
example (s : riscv_state) : «dfn'FSD» (1,2,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

-- fp_memory_FSD_1_7_7
example (s : riscv_state) : «dfn'FSD» (1,7,0) (fixture s 9223372036854775808 16045690984503098046 0 1 255) =
 signalAddressException (ExceptionType.Store_AMO_Fault,9223372036854775808) (fixture s 9223372036854775808 16045690984503098046 0 1 255) := by
  simp [«dfn'FSD», fixture, GPR, gpr, translateAddr, MCSR, privilege, vmType]

end Flapjack.Test.L3FPMemoryParity
