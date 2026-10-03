import Flapjack.RiscV.L3.Defs.ConditionalBranch

set_option maxRecDepth 20000

namespace Flapjack.Test.L3ConditionalBranchParity

open Flapjack.RiscV.L3

private def fixture (s : riscv_state) (mode : BitVec 2) (pc lhs rhs : BitVec 64) : riscv_state :=
 {s with procID := 7, c_PC := fun _ => pc, c_MCSR := fun id => {s.c_MCSR id with mcpuid := {(s.c_MCSR id).mcpuid with ArchBase := mode}}, c_gpr := fun id r => if r = 1 then lhs else if r = 2 then rhs else s.c_gpr id r}

example (s : riscv_state) : «dfn'BEQ» (1,2,1) (fixture s 0 1000 5 5) =
 (let t := (fixture s 0 1000 5 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (((BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) = true := by decide
  change (if (((BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 5) else (fixture s 0 1000 5 5)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,2048) (fixture s 0 1000 5 7) =
 (fixture s 0 1000 5 7) := by
  have condition : (((BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))))) = false := by decide
  change (if (((BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 7) else (fixture s 0 1000 5 7)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,4095) (fixture s 0 18446744073709551614 7 5) =
 (fixture s 0 18446744073709551614 7 5) := by
  have condition : (((BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) = false := by decide
  change (if (((BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 0 18446744073709551614 7 5) else (fixture s 0 18446744073709551614 7 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,1) (fixture s 0 1001 18446744073709551615 0) =
 (fixture s 0 1001 18446744073709551615 0) := by
  have condition : (((BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) = false := by decide
  change (if (((BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1001 18446744073709551615 0) else (fixture s 0 1001 18446744073709551615 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,2) (fixture s 0 1000 0 18446744073709551615) =
 (fixture s 0 1000 0 18446744073709551615) := by
  have condition : (((BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))) = false := by decide
  change (if (((BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 0 1000 0 18446744073709551615) else (fixture s 0 1000 0 18446744073709551615)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,1) (fixture s 0 1000 4294967297 1) =
 (let t := (fixture s 0 1000 4294967297 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (((BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) = true := by decide
  change (if (((BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 4294967297 1) else (fixture s 0 1000 4294967297 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,2047) (fixture s 0 1000 2147483648 1) =
 (fixture s 0 1000 2147483648 1) := by
  have condition : (((BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) = false := by decide
  change (if (((BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 0 1000 2147483648 1) else (fixture s 0 1000 2147483648 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,0) (fixture s 0 1000 9223372036854775808 0) =
 (let t := (fixture s 0 1000 9223372036854775808 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1000)) t.c_NextFetch}) := by
  have condition : (((BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) = true := by decide
  change (if (((BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 0 1000 9223372036854775808 0) else (fixture s 0 1000 9223372036854775808 0)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) = (1000 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,1) (fixture s 2 1000 5 5) =
 (let t := (fixture s 2 1000 5 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : ((((5 : BitVec 64)) == ((5 : BitVec 64)))) = true := by decide
  change (if ((((5 : BitVec 64)) == ((5 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 5) else (fixture s 2 1000 5 5)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,2048) (fixture s 2 1000 5 7) =
 (fixture s 2 1000 5 7) := by
  have condition : ((((5 : BitVec 64)) == ((7 : BitVec 64)))) = false := by decide
  change (if ((((5 : BitVec 64)) == ((7 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 7) else (fixture s 2 1000 5 7)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,4095) (fixture s 2 18446744073709551614 7 5) =
 (fixture s 2 18446744073709551614 7 5) := by
  have condition : ((((7 : BitVec 64)) == ((5 : BitVec 64)))) = false := by decide
  change (if ((((7 : BitVec 64)) == ((5 : BitVec 64)))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 2 18446744073709551614 7 5) else (fixture s 2 18446744073709551614 7 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,1) (fixture s 2 1001 18446744073709551615 0) =
 (fixture s 2 1001 18446744073709551615 0) := by
  have condition : ((((18446744073709551615 : BitVec 64)) == ((0 : BitVec 64)))) = false := by decide
  change (if ((((18446744073709551615 : BitVec 64)) == ((0 : BitVec 64)))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1001 18446744073709551615 0) else (fixture s 2 1001 18446744073709551615 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,2) (fixture s 2 1000 0 18446744073709551615) =
 (fixture s 2 1000 0 18446744073709551615) := by
  have condition : ((((0 : BitVec 64)) == ((18446744073709551615 : BitVec 64)))) = false := by decide
  change (if ((((0 : BitVec 64)) == ((18446744073709551615 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 2 1000 0 18446744073709551615) else (fixture s 2 1000 0 18446744073709551615)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,1) (fixture s 2 1000 4294967297 1) =
 (fixture s 2 1000 4294967297 1) := by
  have condition : ((((4294967297 : BitVec 64)) == ((1 : BitVec 64)))) = false := by decide
  change (if ((((4294967297 : BitVec 64)) == ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 4294967297 1) else (fixture s 2 1000 4294967297 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,2047) (fixture s 2 1000 2147483648 1) =
 (fixture s 2 1000 2147483648 1) := by
  have condition : ((((2147483648 : BitVec 64)) == ((1 : BitVec 64)))) = false := by decide
  change (if ((((2147483648 : BitVec 64)) == ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 2 1000 2147483648 1) else (fixture s 2 1000 2147483648 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,0) (fixture s 2 1000 9223372036854775808 0) =
 (fixture s 2 1000 9223372036854775808 0) := by
  have condition : ((((9223372036854775808 : BitVec 64)) == ((0 : BitVec 64)))) = false := by decide
  change (if ((((9223372036854775808 : BitVec 64)) == ((0 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 2 1000 9223372036854775808 0) else (fixture s 2 1000 9223372036854775808 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,1) (fixture s 3 1000 5 5) =
 (let t := (fixture s 3 1000 5 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : ((((5 : BitVec 64)) == ((5 : BitVec 64)))) = true := by decide
  change (if ((((5 : BitVec 64)) == ((5 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 5) else (fixture s 3 1000 5 5)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,2048) (fixture s 3 1000 5 7) =
 (fixture s 3 1000 5 7) := by
  have condition : ((((5 : BitVec 64)) == ((7 : BitVec 64)))) = false := by decide
  change (if ((((5 : BitVec 64)) == ((7 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 7) else (fixture s 3 1000 5 7)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,4095) (fixture s 3 18446744073709551614 7 5) =
 (fixture s 3 18446744073709551614 7 5) := by
  have condition : ((((7 : BitVec 64)) == ((5 : BitVec 64)))) = false := by decide
  change (if ((((7 : BitVec 64)) == ((5 : BitVec 64)))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 3 18446744073709551614 7 5) else (fixture s 3 18446744073709551614 7 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,1) (fixture s 3 1001 18446744073709551615 0) =
 (fixture s 3 1001 18446744073709551615 0) := by
  have condition : ((((18446744073709551615 : BitVec 64)) == ((0 : BitVec 64)))) = false := by decide
  change (if ((((18446744073709551615 : BitVec 64)) == ((0 : BitVec 64)))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1001 18446744073709551615 0) else (fixture s 3 1001 18446744073709551615 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,2) (fixture s 3 1000 0 18446744073709551615) =
 (fixture s 3 1000 0 18446744073709551615) := by
  have condition : ((((0 : BitVec 64)) == ((18446744073709551615 : BitVec 64)))) = false := by decide
  change (if ((((0 : BitVec 64)) == ((18446744073709551615 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 3 1000 0 18446744073709551615) else (fixture s 3 1000 0 18446744073709551615)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,1) (fixture s 3 1000 4294967297 1) =
 (fixture s 3 1000 4294967297 1) := by
  have condition : ((((4294967297 : BitVec 64)) == ((1 : BitVec 64)))) = false := by decide
  change (if ((((4294967297 : BitVec 64)) == ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 4294967297 1) else (fixture s 3 1000 4294967297 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,2047) (fixture s 3 1000 2147483648 1) =
 (fixture s 3 1000 2147483648 1) := by
  have condition : ((((2147483648 : BitVec 64)) == ((1 : BitVec 64)))) = false := by decide
  change (if ((((2147483648 : BitVec 64)) == ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 3 1000 2147483648 1) else (fixture s 3 1000 2147483648 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BEQ» (1,2,0) (fixture s 3 1000 9223372036854775808 0) =
 (fixture s 3 1000 9223372036854775808 0) := by
  have condition : ((((9223372036854775808 : BitVec 64)) == ((0 : BitVec 64)))) = false := by decide
  change (if ((((9223372036854775808 : BitVec 64)) == ((0 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 3 1000 9223372036854775808 0) else (fixture s 3 1000 9223372036854775808 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,1) (fixture s 0 1000 5 5) =
 (fixture s 0 1000 5 5) := by
  have condition : (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) = false := by decide
  change (if (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 5) else (fixture s 0 1000 5 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,2048) (fixture s 0 1000 5 7) =
 (let t := (fixture s 0 1000 5 7); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709548520)) t.c_NextFetch}) := by
  have condition : (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))))) = true := by decide
  change (if (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 7) else (fixture s 0 1000 5 7)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) = (18446744073709548520 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,4095) (fixture s 0 18446744073709551614 7 5) =
 (let t := (fixture s 0 18446744073709551614 7 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551612)) t.c_NextFetch}) := by
  have condition : (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) = true := by decide
  change (if (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 0 18446744073709551614 7 5) else (fixture s 0 18446744073709551614 7 5)) = _
  rw [condition]
  have target : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,1) (fixture s 0 1001 18446744073709551615 0) =
 (let t := (fixture s 0 1001 18446744073709551615 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1003)) t.c_NextFetch}) := by
  have condition : (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) = true := by decide
  change (if (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1001 18446744073709551615 0) else (fixture s 0 1001 18446744073709551615 0)) = _
  rw [condition]
  have target : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1003 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,2) (fixture s 0 1000 0 18446744073709551615) =
 (let t := (fixture s 0 1000 0 18446744073709551615); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1004)) t.c_NextFetch}) := by
  have condition : (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))) = true := by decide
  change (if (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 0 1000 0 18446744073709551615) else (fixture s 0 1000 0 18446744073709551615)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) = (1004 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,1) (fixture s 0 1000 4294967297 1) =
 (fixture s 0 1000 4294967297 1) := by
  have condition : (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) = false := by decide
  change (if (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 4294967297 1) else (fixture s 0 1000 4294967297 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,2047) (fixture s 0 1000 2147483648 1) =
 (let t := (fixture s 0 1000 2147483648 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 5094)) t.c_NextFetch}) := by
  have condition : (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) = true := by decide
  change (if (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 0 1000 2147483648 1) else (fixture s 0 1000 2147483648 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) = (5094 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,0) (fixture s 0 1000 9223372036854775808 0) =
 (fixture s 0 1000 9223372036854775808 0) := by
  have condition : (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) = false := by decide
  change (if (!((BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 0 1000 9223372036854775808 0) else (fixture s 0 1000 9223372036854775808 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,1) (fixture s 2 1000 5 5) =
 (fixture s 2 1000 5 5) := by
  have condition : (!(((5 : BitVec 64)) == ((5 : BitVec 64)))) = false := by decide
  change (if (!(((5 : BitVec 64)) == ((5 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 5) else (fixture s 2 1000 5 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,2048) (fixture s 2 1000 5 7) =
 (let t := (fixture s 2 1000 5 7); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709548520)) t.c_NextFetch}) := by
  have condition : (!(((5 : BitVec 64)) == ((7 : BitVec 64)))) = true := by decide
  change (if (!(((5 : BitVec 64)) == ((7 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 7) else (fixture s 2 1000 5 7)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) = (18446744073709548520 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,4095) (fixture s 2 18446744073709551614 7 5) =
 (let t := (fixture s 2 18446744073709551614 7 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551612)) t.c_NextFetch}) := by
  have condition : (!(((7 : BitVec 64)) == ((5 : BitVec 64)))) = true := by decide
  change (if (!(((7 : BitVec 64)) == ((5 : BitVec 64)))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 2 18446744073709551614 7 5) else (fixture s 2 18446744073709551614 7 5)) = _
  rw [condition]
  have target : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,1) (fixture s 2 1001 18446744073709551615 0) =
 (let t := (fixture s 2 1001 18446744073709551615 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1003)) t.c_NextFetch}) := by
  have condition : (!(((18446744073709551615 : BitVec 64)) == ((0 : BitVec 64)))) = true := by decide
  change (if (!(((18446744073709551615 : BitVec 64)) == ((0 : BitVec 64)))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1001 18446744073709551615 0) else (fixture s 2 1001 18446744073709551615 0)) = _
  rw [condition]
  have target : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1003 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,2) (fixture s 2 1000 0 18446744073709551615) =
 (let t := (fixture s 2 1000 0 18446744073709551615); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1004)) t.c_NextFetch}) := by
  have condition : (!(((0 : BitVec 64)) == ((18446744073709551615 : BitVec 64)))) = true := by decide
  change (if (!(((0 : BitVec 64)) == ((18446744073709551615 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 2 1000 0 18446744073709551615) else (fixture s 2 1000 0 18446744073709551615)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) = (1004 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,1) (fixture s 2 1000 4294967297 1) =
 (let t := (fixture s 2 1000 4294967297 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (!(((4294967297 : BitVec 64)) == ((1 : BitVec 64)))) = true := by decide
  change (if (!(((4294967297 : BitVec 64)) == ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 4294967297 1) else (fixture s 2 1000 4294967297 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,2047) (fixture s 2 1000 2147483648 1) =
 (let t := (fixture s 2 1000 2147483648 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 5094)) t.c_NextFetch}) := by
  have condition : (!(((2147483648 : BitVec 64)) == ((1 : BitVec 64)))) = true := by decide
  change (if (!(((2147483648 : BitVec 64)) == ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 2 1000 2147483648 1) else (fixture s 2 1000 2147483648 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) = (5094 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,0) (fixture s 2 1000 9223372036854775808 0) =
 (let t := (fixture s 2 1000 9223372036854775808 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1000)) t.c_NextFetch}) := by
  have condition : (!(((9223372036854775808 : BitVec 64)) == ((0 : BitVec 64)))) = true := by decide
  change (if (!(((9223372036854775808 : BitVec 64)) == ((0 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 2 1000 9223372036854775808 0) else (fixture s 2 1000 9223372036854775808 0)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) = (1000 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,1) (fixture s 3 1000 5 5) =
 (fixture s 3 1000 5 5) := by
  have condition : (!(((5 : BitVec 64)) == ((5 : BitVec 64)))) = false := by decide
  change (if (!(((5 : BitVec 64)) == ((5 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 5) else (fixture s 3 1000 5 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,2048) (fixture s 3 1000 5 7) =
 (let t := (fixture s 3 1000 5 7); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709548520)) t.c_NextFetch}) := by
  have condition : (!(((5 : BitVec 64)) == ((7 : BitVec 64)))) = true := by decide
  change (if (!(((5 : BitVec 64)) == ((7 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 7) else (fixture s 3 1000 5 7)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) = (18446744073709548520 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,4095) (fixture s 3 18446744073709551614 7 5) =
 (let t := (fixture s 3 18446744073709551614 7 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551612)) t.c_NextFetch}) := by
  have condition : (!(((7 : BitVec 64)) == ((5 : BitVec 64)))) = true := by decide
  change (if (!(((7 : BitVec 64)) == ((5 : BitVec 64)))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 3 18446744073709551614 7 5) else (fixture s 3 18446744073709551614 7 5)) = _
  rw [condition]
  have target : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,1) (fixture s 3 1001 18446744073709551615 0) =
 (let t := (fixture s 3 1001 18446744073709551615 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1003)) t.c_NextFetch}) := by
  have condition : (!(((18446744073709551615 : BitVec 64)) == ((0 : BitVec 64)))) = true := by decide
  change (if (!(((18446744073709551615 : BitVec 64)) == ((0 : BitVec 64)))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1001 18446744073709551615 0) else (fixture s 3 1001 18446744073709551615 0)) = _
  rw [condition]
  have target : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1003 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,2) (fixture s 3 1000 0 18446744073709551615) =
 (let t := (fixture s 3 1000 0 18446744073709551615); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1004)) t.c_NextFetch}) := by
  have condition : (!(((0 : BitVec 64)) == ((18446744073709551615 : BitVec 64)))) = true := by decide
  change (if (!(((0 : BitVec 64)) == ((18446744073709551615 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 3 1000 0 18446744073709551615) else (fixture s 3 1000 0 18446744073709551615)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) = (1004 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,1) (fixture s 3 1000 4294967297 1) =
 (let t := (fixture s 3 1000 4294967297 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (!(((4294967297 : BitVec 64)) == ((1 : BitVec 64)))) = true := by decide
  change (if (!(((4294967297 : BitVec 64)) == ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 4294967297 1) else (fixture s 3 1000 4294967297 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,2047) (fixture s 3 1000 2147483648 1) =
 (let t := (fixture s 3 1000 2147483648 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 5094)) t.c_NextFetch}) := by
  have condition : (!(((2147483648 : BitVec 64)) == ((1 : BitVec 64)))) = true := by decide
  change (if (!(((2147483648 : BitVec 64)) == ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 3 1000 2147483648 1) else (fixture s 3 1000 2147483648 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) = (5094 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BNE» (1,2,0) (fixture s 3 1000 9223372036854775808 0) =
 (let t := (fixture s 3 1000 9223372036854775808 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1000)) t.c_NextFetch}) := by
  have condition : (!(((9223372036854775808 : BitVec 64)) == ((0 : BitVec 64)))) = true := by decide
  change (if (!(((9223372036854775808 : BitVec 64)) == ((0 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 3 1000 9223372036854775808 0) else (fixture s 3 1000 9223372036854775808 0)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) = (1000 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,1) (fixture s 0 1000 5 5) =
 (fixture s 0 1000 5 5) := by
  have condition : (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) = false := by decide
  change (if (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 5) else (fixture s 0 1000 5 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,2048) (fixture s 0 1000 5 7) =
 (let t := (fixture s 0 1000 5 7); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709548520)) t.c_NextFetch}) := by
  have condition : (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))) = true := by decide
  change (if (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 7) else (fixture s 0 1000 5 7)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) = (18446744073709548520 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,4095) (fixture s 0 18446744073709551614 7 5) =
 (fixture s 0 18446744073709551614 7 5) := by
  have condition : (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) = false := by decide
  change (if (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 0 18446744073709551614 7 5) else (fixture s 0 18446744073709551614 7 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,1) (fixture s 0 1001 18446744073709551615 0) =
 (let t := (fixture s 0 1001 18446744073709551615 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1003)) t.c_NextFetch}) := by
  have condition : (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) = true := by decide
  change (if (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1001 18446744073709551615 0) else (fixture s 0 1001 18446744073709551615 0)) = _
  rw [condition]
  have target : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1003 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,2) (fixture s 0 1000 0 18446744073709551615) =
 (fixture s 0 1000 0 18446744073709551615) := by
  have condition : (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) = false := by decide
  change (if (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 0 1000 0 18446744073709551615) else (fixture s 0 1000 0 18446744073709551615)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,1) (fixture s 0 1000 4294967297 1) =
 (fixture s 0 1000 4294967297 1) := by
  have condition : (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))) = false := by decide
  change (if (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 4294967297 1) else (fixture s 0 1000 4294967297 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,2047) (fixture s 0 1000 2147483648 1) =
 (let t := (fixture s 0 1000 2147483648 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 5094)) t.c_NextFetch}) := by
  have condition : (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))) = true := by decide
  change (if (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 0 1000 2147483648 1) else (fixture s 0 1000 2147483648 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) = (5094 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,0) (fixture s 0 1000 9223372036854775808 0) =
 (fixture s 0 1000 9223372036854775808 0) := by
  have condition : (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) = false := by decide
  change (if (BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 0 1000 9223372036854775808 0) else (fixture s 0 1000 9223372036854775808 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,1) (fixture s 2 1000 5 5) =
 (fixture s 2 1000 5 5) := by
  have condition : (BitVec.slt ((5 : BitVec 64)) ((5 : BitVec 64))) = false := by decide
  change (if (BitVec.slt ((5 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 5) else (fixture s 2 1000 5 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,2048) (fixture s 2 1000 5 7) =
 (let t := (fixture s 2 1000 5 7); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709548520)) t.c_NextFetch}) := by
  have condition : (BitVec.slt ((5 : BitVec 64)) ((7 : BitVec 64))) = true := by decide
  change (if (BitVec.slt ((5 : BitVec 64)) ((7 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 7) else (fixture s 2 1000 5 7)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) = (18446744073709548520 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,4095) (fixture s 2 18446744073709551614 7 5) =
 (fixture s 2 18446744073709551614 7 5) := by
  have condition : (BitVec.slt ((7 : BitVec 64)) ((5 : BitVec 64))) = false := by decide
  change (if (BitVec.slt ((7 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 2 18446744073709551614 7 5) else (fixture s 2 18446744073709551614 7 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,1) (fixture s 2 1001 18446744073709551615 0) =
 (let t := (fixture s 2 1001 18446744073709551615 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1003)) t.c_NextFetch}) := by
  have condition : (BitVec.slt ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) = true := by decide
  change (if (BitVec.slt ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1001 18446744073709551615 0) else (fixture s 2 1001 18446744073709551615 0)) = _
  rw [condition]
  have target : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1003 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,2) (fixture s 2 1000 0 18446744073709551615) =
 (fixture s 2 1000 0 18446744073709551615) := by
  have condition : (BitVec.slt ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) = false := by decide
  change (if (BitVec.slt ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 2 1000 0 18446744073709551615) else (fixture s 2 1000 0 18446744073709551615)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,1) (fixture s 2 1000 4294967297 1) =
 (fixture s 2 1000 4294967297 1) := by
  have condition : (BitVec.slt ((4294967297 : BitVec 64)) ((1 : BitVec 64))) = false := by decide
  change (if (BitVec.slt ((4294967297 : BitVec 64)) ((1 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 4294967297 1) else (fixture s 2 1000 4294967297 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,2047) (fixture s 2 1000 2147483648 1) =
 (fixture s 2 1000 2147483648 1) := by
  have condition : (BitVec.slt ((2147483648 : BitVec 64)) ((1 : BitVec 64))) = false := by decide
  change (if (BitVec.slt ((2147483648 : BitVec 64)) ((1 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 2 1000 2147483648 1) else (fixture s 2 1000 2147483648 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,0) (fixture s 2 1000 9223372036854775808 0) =
 (let t := (fixture s 2 1000 9223372036854775808 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1000)) t.c_NextFetch}) := by
  have condition : (BitVec.slt ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64))) = true := by decide
  change (if (BitVec.slt ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 2 1000 9223372036854775808 0) else (fixture s 2 1000 9223372036854775808 0)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) = (1000 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,1) (fixture s 3 1000 5 5) =
 (fixture s 3 1000 5 5) := by
  have condition : (BitVec.slt ((5 : BitVec 64)) ((5 : BitVec 64))) = false := by decide
  change (if (BitVec.slt ((5 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 5) else (fixture s 3 1000 5 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,2048) (fixture s 3 1000 5 7) =
 (let t := (fixture s 3 1000 5 7); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709548520)) t.c_NextFetch}) := by
  have condition : (BitVec.slt ((5 : BitVec 64)) ((7 : BitVec 64))) = true := by decide
  change (if (BitVec.slt ((5 : BitVec 64)) ((7 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 7) else (fixture s 3 1000 5 7)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) = (18446744073709548520 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,4095) (fixture s 3 18446744073709551614 7 5) =
 (fixture s 3 18446744073709551614 7 5) := by
  have condition : (BitVec.slt ((7 : BitVec 64)) ((5 : BitVec 64))) = false := by decide
  change (if (BitVec.slt ((7 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 3 18446744073709551614 7 5) else (fixture s 3 18446744073709551614 7 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,1) (fixture s 3 1001 18446744073709551615 0) =
 (let t := (fixture s 3 1001 18446744073709551615 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1003)) t.c_NextFetch}) := by
  have condition : (BitVec.slt ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) = true := by decide
  change (if (BitVec.slt ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1001 18446744073709551615 0) else (fixture s 3 1001 18446744073709551615 0)) = _
  rw [condition]
  have target : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1003 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,2) (fixture s 3 1000 0 18446744073709551615) =
 (fixture s 3 1000 0 18446744073709551615) := by
  have condition : (BitVec.slt ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) = false := by decide
  change (if (BitVec.slt ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 3 1000 0 18446744073709551615) else (fixture s 3 1000 0 18446744073709551615)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,1) (fixture s 3 1000 4294967297 1) =
 (fixture s 3 1000 4294967297 1) := by
  have condition : (BitVec.slt ((4294967297 : BitVec 64)) ((1 : BitVec 64))) = false := by decide
  change (if (BitVec.slt ((4294967297 : BitVec 64)) ((1 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 4294967297 1) else (fixture s 3 1000 4294967297 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,2047) (fixture s 3 1000 2147483648 1) =
 (fixture s 3 1000 2147483648 1) := by
  have condition : (BitVec.slt ((2147483648 : BitVec 64)) ((1 : BitVec 64))) = false := by decide
  change (if (BitVec.slt ((2147483648 : BitVec 64)) ((1 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 3 1000 2147483648 1) else (fixture s 3 1000 2147483648 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLT» (1,2,0) (fixture s 3 1000 9223372036854775808 0) =
 (let t := (fixture s 3 1000 9223372036854775808 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1000)) t.c_NextFetch}) := by
  have condition : (BitVec.slt ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64))) = true := by decide
  change (if (BitVec.slt ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 3 1000 9223372036854775808 0) else (fixture s 3 1000 9223372036854775808 0)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) = (1000 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,1) (fixture s 0 1000 5 5) =
 (let t := (fixture s 0 1000 5 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) = true := by decide
  change (if (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 5) else (fixture s 0 1000 5 5)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,2048) (fixture s 0 1000 5 7) =
 (fixture s 0 1000 5 7) := by
  have condition : (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) = false := by decide
  change (if (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 7) else (fixture s 0 1000 5 7)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,4095) (fixture s 0 18446744073709551614 7 5) =
 (let t := (fixture s 0 18446744073709551614 7 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551612)) t.c_NextFetch}) := by
  have condition : (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))) = true := by decide
  change (if (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 0 18446744073709551614 7 5) else (fixture s 0 18446744073709551614 7 5)) = _
  rw [condition]
  have target : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,1) (fixture s 0 1001 18446744073709551615 0) =
 (fixture s 0 1001 18446744073709551615 0) := by
  have condition : (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) = false := by decide
  change (if (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1001 18446744073709551615 0) else (fixture s 0 1001 18446744073709551615 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,2) (fixture s 0 1000 0 18446744073709551615) =
 (let t := (fixture s 0 1000 0 18446744073709551615); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1004)) t.c_NextFetch}) := by
  have condition : (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) = true := by decide
  change (if (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 0 1000 0 18446744073709551615) else (fixture s 0 1000 0 18446744073709551615)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) = (1004 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,1) (fixture s 0 1000 4294967297 1) =
 (let t := (fixture s 0 1000 4294967297 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))) = true := by decide
  change (if (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 4294967297 1) else (fixture s 0 1000 4294967297 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,2047) (fixture s 0 1000 2147483648 1) =
 (fixture s 0 1000 2147483648 1) := by
  have condition : (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))) = false := by decide
  change (if (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 0 1000 2147483648 1) else (fixture s 0 1000 2147483648 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,0) (fixture s 0 1000 9223372036854775808 0) =
 (let t := (fixture s 0 1000 9223372036854775808 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1000)) t.c_NextFetch}) := by
  have condition : (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) = true := by decide
  change (if (BitVec.sle (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 0 1000 9223372036854775808 0) else (fixture s 0 1000 9223372036854775808 0)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) = (1000 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,1) (fixture s 2 1000 5 5) =
 (let t := (fixture s 2 1000 5 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (BitVec.sle ((5 : BitVec 64)) ((5 : BitVec 64))) = true := by decide
  change (if (BitVec.sle ((5 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 5) else (fixture s 2 1000 5 5)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,2048) (fixture s 2 1000 5 7) =
 (fixture s 2 1000 5 7) := by
  have condition : (BitVec.sle ((7 : BitVec 64)) ((5 : BitVec 64))) = false := by decide
  change (if (BitVec.sle ((7 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 7) else (fixture s 2 1000 5 7)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,4095) (fixture s 2 18446744073709551614 7 5) =
 (let t := (fixture s 2 18446744073709551614 7 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551612)) t.c_NextFetch}) := by
  have condition : (BitVec.sle ((5 : BitVec 64)) ((7 : BitVec 64))) = true := by decide
  change (if (BitVec.sle ((5 : BitVec 64)) ((7 : BitVec 64))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 2 18446744073709551614 7 5) else (fixture s 2 18446744073709551614 7 5)) = _
  rw [condition]
  have target : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,1) (fixture s 2 1001 18446744073709551615 0) =
 (fixture s 2 1001 18446744073709551615 0) := by
  have condition : (BitVec.sle ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) = false := by decide
  change (if (BitVec.sle ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1001 18446744073709551615 0) else (fixture s 2 1001 18446744073709551615 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,2) (fixture s 2 1000 0 18446744073709551615) =
 (let t := (fixture s 2 1000 0 18446744073709551615); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1004)) t.c_NextFetch}) := by
  have condition : (BitVec.sle ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) = true := by decide
  change (if (BitVec.sle ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 2 1000 0 18446744073709551615) else (fixture s 2 1000 0 18446744073709551615)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) = (1004 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,1) (fixture s 2 1000 4294967297 1) =
 (let t := (fixture s 2 1000 4294967297 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (BitVec.sle ((1 : BitVec 64)) ((4294967297 : BitVec 64))) = true := by decide
  change (if (BitVec.sle ((1 : BitVec 64)) ((4294967297 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 4294967297 1) else (fixture s 2 1000 4294967297 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,2047) (fixture s 2 1000 2147483648 1) =
 (let t := (fixture s 2 1000 2147483648 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 5094)) t.c_NextFetch}) := by
  have condition : (BitVec.sle ((1 : BitVec 64)) ((2147483648 : BitVec 64))) = true := by decide
  change (if (BitVec.sle ((1 : BitVec 64)) ((2147483648 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 2 1000 2147483648 1) else (fixture s 2 1000 2147483648 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) = (5094 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,0) (fixture s 2 1000 9223372036854775808 0) =
 (fixture s 2 1000 9223372036854775808 0) := by
  have condition : (BitVec.sle ((0 : BitVec 64)) ((9223372036854775808 : BitVec 64))) = false := by decide
  change (if (BitVec.sle ((0 : BitVec 64)) ((9223372036854775808 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 2 1000 9223372036854775808 0) else (fixture s 2 1000 9223372036854775808 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,1) (fixture s 3 1000 5 5) =
 (let t := (fixture s 3 1000 5 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (BitVec.sle ((5 : BitVec 64)) ((5 : BitVec 64))) = true := by decide
  change (if (BitVec.sle ((5 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 5) else (fixture s 3 1000 5 5)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,2048) (fixture s 3 1000 5 7) =
 (fixture s 3 1000 5 7) := by
  have condition : (BitVec.sle ((7 : BitVec 64)) ((5 : BitVec 64))) = false := by decide
  change (if (BitVec.sle ((7 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 7) else (fixture s 3 1000 5 7)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,4095) (fixture s 3 18446744073709551614 7 5) =
 (let t := (fixture s 3 18446744073709551614 7 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551612)) t.c_NextFetch}) := by
  have condition : (BitVec.sle ((5 : BitVec 64)) ((7 : BitVec 64))) = true := by decide
  change (if (BitVec.sle ((5 : BitVec 64)) ((7 : BitVec 64))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 3 18446744073709551614 7 5) else (fixture s 3 18446744073709551614 7 5)) = _
  rw [condition]
  have target : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,1) (fixture s 3 1001 18446744073709551615 0) =
 (fixture s 3 1001 18446744073709551615 0) := by
  have condition : (BitVec.sle ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) = false := by decide
  change (if (BitVec.sle ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1001 18446744073709551615 0) else (fixture s 3 1001 18446744073709551615 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,2) (fixture s 3 1000 0 18446744073709551615) =
 (let t := (fixture s 3 1000 0 18446744073709551615); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1004)) t.c_NextFetch}) := by
  have condition : (BitVec.sle ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) = true := by decide
  change (if (BitVec.sle ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 3 1000 0 18446744073709551615) else (fixture s 3 1000 0 18446744073709551615)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) = (1004 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,1) (fixture s 3 1000 4294967297 1) =
 (let t := (fixture s 3 1000 4294967297 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (BitVec.sle ((1 : BitVec 64)) ((4294967297 : BitVec 64))) = true := by decide
  change (if (BitVec.sle ((1 : BitVec 64)) ((4294967297 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 4294967297 1) else (fixture s 3 1000 4294967297 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,2047) (fixture s 3 1000 2147483648 1) =
 (let t := (fixture s 3 1000 2147483648 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 5094)) t.c_NextFetch}) := by
  have condition : (BitVec.sle ((1 : BitVec 64)) ((2147483648 : BitVec 64))) = true := by decide
  change (if (BitVec.sle ((1 : BitVec 64)) ((2147483648 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 3 1000 2147483648 1) else (fixture s 3 1000 2147483648 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) = (5094 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGE» (1,2,0) (fixture s 3 1000 9223372036854775808 0) =
 (fixture s 3 1000 9223372036854775808 0) := by
  have condition : (BitVec.sle ((0 : BitVec 64)) ((9223372036854775808 : BitVec 64))) = false := by decide
  change (if (BitVec.sle ((0 : BitVec 64)) ((9223372036854775808 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 3 1000 9223372036854775808 0) else (fixture s 3 1000 9223372036854775808 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,1) (fixture s 0 1000 5 5) =
 (fixture s 0 1000 5 5) := by
  have condition : (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) = false := by decide
  change (if (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 5) else (fixture s 0 1000 5 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,2048) (fixture s 0 1000 5 7) =
 (let t := (fixture s 0 1000 5 7); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709548520)) t.c_NextFetch}) := by
  have condition : (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))) = true := by decide
  change (if (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 7) else (fixture s 0 1000 5 7)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) = (18446744073709548520 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,4095) (fixture s 0 18446744073709551614 7 5) =
 (fixture s 0 18446744073709551614 7 5) := by
  have condition : (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) = false := by decide
  change (if (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 0 18446744073709551614 7 5) else (fixture s 0 18446744073709551614 7 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,1) (fixture s 0 1001 18446744073709551615 0) =
 (fixture s 0 1001 18446744073709551615 0) := by
  have condition : (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) = false := by decide
  change (if (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1001 18446744073709551615 0) else (fixture s 0 1001 18446744073709551615 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,2) (fixture s 0 1000 0 18446744073709551615) =
 (let t := (fixture s 0 1000 0 18446744073709551615); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1004)) t.c_NextFetch}) := by
  have condition : (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) = true := by decide
  change (if (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 0 1000 0 18446744073709551615) else (fixture s 0 1000 0 18446744073709551615)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) = (1004 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,1) (fixture s 0 1000 4294967297 1) =
 (fixture s 0 1000 4294967297 1) := by
  have condition : (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))) = false := by decide
  change (if (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 4294967297 1) else (fixture s 0 1000 4294967297 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,2047) (fixture s 0 1000 2147483648 1) =
 (fixture s 0 1000 2147483648 1) := by
  have condition : (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))) = false := by decide
  change (if (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 0 1000 2147483648 1) else (fixture s 0 1000 2147483648 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,0) (fixture s 0 1000 9223372036854775808 0) =
 (fixture s 0 1000 9223372036854775808 0) := by
  have condition : (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) = false := by decide
  change (if (BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 0 1000 9223372036854775808 0) else (fixture s 0 1000 9223372036854775808 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,1) (fixture s 2 1000 5 5) =
 (fixture s 2 1000 5 5) := by
  have condition : (BitVec.ult ((5 : BitVec 64)) ((5 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((5 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 5) else (fixture s 2 1000 5 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,2048) (fixture s 2 1000 5 7) =
 (let t := (fixture s 2 1000 5 7); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709548520)) t.c_NextFetch}) := by
  have condition : (BitVec.ult ((5 : BitVec 64)) ((7 : BitVec 64))) = true := by decide
  change (if (BitVec.ult ((5 : BitVec 64)) ((7 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 7) else (fixture s 2 1000 5 7)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) = (18446744073709548520 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,4095) (fixture s 2 18446744073709551614 7 5) =
 (fixture s 2 18446744073709551614 7 5) := by
  have condition : (BitVec.ult ((7 : BitVec 64)) ((5 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((7 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 2 18446744073709551614 7 5) else (fixture s 2 18446744073709551614 7 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,1) (fixture s 2 1001 18446744073709551615 0) =
 (fixture s 2 1001 18446744073709551615 0) := by
  have condition : (BitVec.ult ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1001 18446744073709551615 0) else (fixture s 2 1001 18446744073709551615 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,2) (fixture s 2 1000 0 18446744073709551615) =
 (let t := (fixture s 2 1000 0 18446744073709551615); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1004)) t.c_NextFetch}) := by
  have condition : (BitVec.ult ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) = true := by decide
  change (if (BitVec.ult ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 2 1000 0 18446744073709551615) else (fixture s 2 1000 0 18446744073709551615)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) = (1004 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,1) (fixture s 2 1000 4294967297 1) =
 (fixture s 2 1000 4294967297 1) := by
  have condition : (BitVec.ult ((4294967297 : BitVec 64)) ((1 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((4294967297 : BitVec 64)) ((1 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 4294967297 1) else (fixture s 2 1000 4294967297 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,2047) (fixture s 2 1000 2147483648 1) =
 (fixture s 2 1000 2147483648 1) := by
  have condition : (BitVec.ult ((2147483648 : BitVec 64)) ((1 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((2147483648 : BitVec 64)) ((1 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 2 1000 2147483648 1) else (fixture s 2 1000 2147483648 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,0) (fixture s 2 1000 9223372036854775808 0) =
 (fixture s 2 1000 9223372036854775808 0) := by
  have condition : (BitVec.ult ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 2 1000 9223372036854775808 0) else (fixture s 2 1000 9223372036854775808 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,1) (fixture s 3 1000 5 5) =
 (fixture s 3 1000 5 5) := by
  have condition : (BitVec.ult ((5 : BitVec 64)) ((5 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((5 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 5) else (fixture s 3 1000 5 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,2048) (fixture s 3 1000 5 7) =
 (let t := (fixture s 3 1000 5 7); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709548520)) t.c_NextFetch}) := by
  have condition : (BitVec.ult ((5 : BitVec 64)) ((7 : BitVec 64))) = true := by decide
  change (if (BitVec.ult ((5 : BitVec 64)) ((7 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 7) else (fixture s 3 1000 5 7)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) = (18446744073709548520 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,4095) (fixture s 3 18446744073709551614 7 5) =
 (fixture s 3 18446744073709551614 7 5) := by
  have condition : (BitVec.ult ((7 : BitVec 64)) ((5 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((7 : BitVec 64)) ((5 : BitVec 64))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 3 18446744073709551614 7 5) else (fixture s 3 18446744073709551614 7 5)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,1) (fixture s 3 1001 18446744073709551615 0) =
 (fixture s 3 1001 18446744073709551615 0) := by
  have condition : (BitVec.ult ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1001 18446744073709551615 0) else (fixture s 3 1001 18446744073709551615 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,2) (fixture s 3 1000 0 18446744073709551615) =
 (let t := (fixture s 3 1000 0 18446744073709551615); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1004)) t.c_NextFetch}) := by
  have condition : (BitVec.ult ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) = true := by decide
  change (if (BitVec.ult ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 3 1000 0 18446744073709551615) else (fixture s 3 1000 0 18446744073709551615)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) = (1004 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,1) (fixture s 3 1000 4294967297 1) =
 (fixture s 3 1000 4294967297 1) := by
  have condition : (BitVec.ult ((4294967297 : BitVec 64)) ((1 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((4294967297 : BitVec 64)) ((1 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 4294967297 1) else (fixture s 3 1000 4294967297 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,2047) (fixture s 3 1000 2147483648 1) =
 (fixture s 3 1000 2147483648 1) := by
  have condition : (BitVec.ult ((2147483648 : BitVec 64)) ((1 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((2147483648 : BitVec 64)) ((1 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 3 1000 2147483648 1) else (fixture s 3 1000 2147483648 1)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BLTU» (1,2,0) (fixture s 3 1000 9223372036854775808 0) =
 (fixture s 3 1000 9223372036854775808 0) := by
  have condition : (BitVec.ult ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64))) = false := by decide
  change (if (BitVec.ult ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 3 1000 9223372036854775808 0) else (fixture s 3 1000 9223372036854775808 0)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,1) (fixture s 0 1000 5 5) =
 (let t := (fixture s 0 1000 5 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) = true := by decide
  change (if (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 5) else (fixture s 0 1000 5 5)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,2048) (fixture s 0 1000 5 7) =
 (fixture s 0 1000 5 7) := by
  have condition : (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))))) = false := by decide
  change (if (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 0 1000 5 7) else (fixture s 0 1000 5 7)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,4095) (fixture s 0 18446744073709551614 7 5) =
 (let t := (fixture s 0 18446744073709551614 7 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551612)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) = true := by decide
  change (if (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 0 18446744073709551614 7 5) else (fixture s 0 18446744073709551614 7 5)) = _
  rw [condition]
  have target : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,1) (fixture s 0 1001 18446744073709551615 0) =
 (let t := (fixture s 0 1001 18446744073709551615 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1003)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) = true := by decide
  change (if (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1001 18446744073709551615 0) else (fixture s 0 1001 18446744073709551615 0)) = _
  rw [condition]
  have target : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1003 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,2) (fixture s 0 1000 0 18446744073709551615) =
 (fixture s 0 1000 0 18446744073709551615) := by
  have condition : (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))) = false := by decide
  change (if (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 0 1000 0 18446744073709551615) else (fixture s 0 1000 0 18446744073709551615)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,1) (fixture s 0 1000 4294967297 1) =
 (let t := (fixture s 0 1000 4294967297 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) = true := by decide
  change (if (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 0 1000 4294967297 1) else (fixture s 0 1000 4294967297 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,2047) (fixture s 0 1000 2147483648 1) =
 (let t := (fixture s 0 1000 2147483648 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 5094)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) = true := by decide
  change (if (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 0 1000 2147483648 1) else (fixture s 0 1000 2147483648 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) = (5094 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,0) (fixture s 0 1000 9223372036854775808 0) =
 (let t := (fixture s 0 1000 9223372036854775808 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1000)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) = true := by decide
  change (if (!(BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 0 1000 9223372036854775808 0) else (fixture s 0 1000 9223372036854775808 0)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) = (1000 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,1) (fixture s 2 1000 5 5) =
 (let t := (fixture s 2 1000 5 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((5 : BitVec 64)) ((5 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((5 : BitVec 64)) ((5 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 5) else (fixture s 2 1000 5 5)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,2048) (fixture s 2 1000 5 7) =
 (fixture s 2 1000 5 7) := by
  have condition : (!(BitVec.ult ((5 : BitVec 64)) ((7 : BitVec 64)))) = false := by decide
  change (if (!(BitVec.ult ((5 : BitVec 64)) ((7 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 2 1000 5 7) else (fixture s 2 1000 5 7)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,4095) (fixture s 2 18446744073709551614 7 5) =
 (let t := (fixture s 2 18446744073709551614 7 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551612)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((7 : BitVec 64)) ((5 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((7 : BitVec 64)) ((5 : BitVec 64)))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 2 18446744073709551614 7 5) else (fixture s 2 18446744073709551614 7 5)) = _
  rw [condition]
  have target : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,1) (fixture s 2 1001 18446744073709551615 0) =
 (let t := (fixture s 2 1001 18446744073709551615 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1003)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64)))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1001 18446744073709551615 0) else (fixture s 2 1001 18446744073709551615 0)) = _
  rw [condition]
  have target : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1003 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,2) (fixture s 2 1000 0 18446744073709551615) =
 (fixture s 2 1000 0 18446744073709551615) := by
  have condition : (!(BitVec.ult ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64)))) = false := by decide
  change (if (!(BitVec.ult ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 2 1000 0 18446744073709551615) else (fixture s 2 1000 0 18446744073709551615)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,1) (fixture s 2 1000 4294967297 1) =
 (let t := (fixture s 2 1000 4294967297 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((4294967297 : BitVec 64)) ((1 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((4294967297 : BitVec 64)) ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 2 1000 4294967297 1) else (fixture s 2 1000 4294967297 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,2047) (fixture s 2 1000 2147483648 1) =
 (let t := (fixture s 2 1000 2147483648 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 5094)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((2147483648 : BitVec 64)) ((1 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((2147483648 : BitVec 64)) ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 2 1000 2147483648 1) else (fixture s 2 1000 2147483648 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) = (5094 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,0) (fixture s 2 1000 9223372036854775808 0) =
 (let t := (fixture s 2 1000 9223372036854775808 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1000)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 2 1000 9223372036854775808 0) else (fixture s 2 1000 9223372036854775808 0)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) = (1000 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,1) (fixture s 3 1000 5 5) =
 (let t := (fixture s 3 1000 5 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((5 : BitVec 64)) ((5 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((5 : BitVec 64)) ((5 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 5) else (fixture s 3 1000 5 5)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,2048) (fixture s 3 1000 5 7) =
 (fixture s 3 1000 5 7) := by
  have condition : (!(BitVec.ult ((5 : BitVec 64)) ((7 : BitVec 64)))) = false := by decide
  change (if (!(BitVec.ult ((5 : BitVec 64)) ((7 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2048 : BitVec 12)) <<< 1)) (fixture s 3 1000 5 7) else (fixture s 3 1000 5 7)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,4095) (fixture s 3 18446744073709551614 7 5) =
 (let t := (fixture s 3 18446744073709551614 7 5); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551612)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((7 : BitVec 64)) ((5 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((7 : BitVec 64)) ((5 : BitVec 64)))) then branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) (fixture s 3 18446744073709551614 7 5) else (fixture s 3 18446744073709551614 7 5)) = _
  rw [condition]
  have target : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (4095 : BitVec 12)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,1) (fixture s 3 1001 18446744073709551615 0) =
 (let t := (fixture s 3 1001 18446744073709551615 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1003)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((18446744073709551615 : BitVec 64)) ((0 : BitVec 64)))) then branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1001 18446744073709551615 0) else (fixture s 3 1001 18446744073709551615 0)) = _
  rw [condition]
  have target : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1003 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,2) (fixture s 3 1000 0 18446744073709551615) =
 (fixture s 3 1000 0 18446744073709551615) := by
  have condition : (!(BitVec.ult ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64)))) = false := by decide
  change (if (!(BitVec.ult ((0 : BitVec 64)) ((18446744073709551615 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2 : BitVec 12)) <<< 1)) (fixture s 3 1000 0 18446744073709551615) else (fixture s 3 1000 0 18446744073709551615)) = _
  rw [condition]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,1) (fixture s 3 1000 4294967297 1) =
 (let t := (fixture s 3 1000 4294967297 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1002)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((4294967297 : BitVec 64)) ((1 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((4294967297 : BitVec 64)) ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) (fixture s 3 1000 4294967297 1) else (fixture s 3 1000 4294967297 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 12)) <<< 1)) = (1002 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,2047) (fixture s 3 1000 2147483648 1) =
 (let t := (fixture s 3 1000 2147483648 1); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 5094)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((2147483648 : BitVec 64)) ((1 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((2147483648 : BitVec 64)) ((1 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) (fixture s 3 1000 2147483648 1) else (fixture s 3 1000 2147483648 1)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (2047 : BitVec 12)) <<< 1)) = (5094 : BitVec 64) := by decide
  rw [target]
  rfl

example (s : riscv_state) : «dfn'BGEU» (1,2,0) (fixture s 3 1000 9223372036854775808 0) =
 (let t := (fixture s 3 1000 9223372036854775808 0); {t with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 1000)) t.c_NextFetch}) := by
  have condition : (!(BitVec.ult ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64)))) = true := by decide
  change (if (!(BitVec.ult ((9223372036854775808 : BitVec 64)) ((0 : BitVec 64)))) then branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) (fixture s 3 1000 9223372036854775808 0) else (fixture s 3 1000 9223372036854775808 0)) = _
  rw [condition]
  have target : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 12)) <<< 1)) = (1000 : BitVec 64) := by decide
  rw [target]
  rfl

private def unknownMessage : List (BitVec 8) :=
 [85,110,107,110,111,119,110,32,97,114,99,104,105,116,101,99,116,117,114,101,58,32,49]

example (s : riscv_state) : «dfn'BEQ» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 999)) u.c_NextFetch}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BEQ», fixture, in32BitMode, curArch, architecture, MCSR, PC, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, branchTo, «write'NextFetch»]
  all_goals try rw [zero]
  all_goals simp

example (s : riscv_state) : «dfn'BEQ» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 999)) u.c_NextFetch}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BEQ», fixture, in32BitMode, curArch, architecture, MCSR, PC, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, branchTo, «write'NextFetch»]
  all_goals try rw [zero]
  all_goals simp

example (s : riscv_state) : «dfn'BNE» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.NoException}; {t with exception := exception.UNDEFINED unknownMessage}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BNE», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
  all_goals try rw [zero]
  all_goals simp

example (s : riscv_state) : «dfn'BNE» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}; {t with exception := exception.UNDEFINED [9]}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BNE», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
  all_goals try rw [zero]
  all_goals simp

example (s : riscv_state) : «dfn'BLT» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.NoException}; {t with exception := exception.UNDEFINED unknownMessage}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BLT», fixture, in32BitMode, curArch, architecture, MCSR, PC, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, branchTo, «write'NextFetch»]
  all_goals try rw [zero]
  all_goals simp [BitVec.slt]

example (s : riscv_state) : «dfn'BLT» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}; {t with exception := exception.UNDEFINED [9]}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BLT», fixture, in32BitMode, curArch, architecture, MCSR, PC, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, branchTo, «write'NextFetch»]
  all_goals try rw [zero]
  all_goals simp [BitVec.slt]

example (s : riscv_state) : «dfn'BGE» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 999)) u.c_NextFetch}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BGE», fixture, in32BitMode, curArch, architecture, MCSR, PC, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, branchTo, «write'NextFetch»]
  all_goals try rw [zero]
  all_goals simp [BitVec.sle]

example (s : riscv_state) : «dfn'BGE» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 999)) u.c_NextFetch}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BGE», fixture, in32BitMode, curArch, architecture, MCSR, PC, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, branchTo, «write'NextFetch»]
  all_goals try rw [zero]
  all_goals simp [BitVec.sle]

example (s : riscv_state) : «dfn'BLTU» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.NoException}; {t with exception := exception.UNDEFINED unknownMessage}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BLTU», fixture, in32BitMode, curArch, architecture, MCSR, PC, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, branchTo, «write'NextFetch»]
  all_goals try rw [zero]
  all_goals simp [BitVec.ult]

example (s : riscv_state) : «dfn'BLTU» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}; {t with exception := exception.UNDEFINED [9]}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BLTU», fixture, in32BitMode, curArch, architecture, MCSR, PC, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, branchTo, «write'NextFetch»]
  all_goals try rw [zero]
  all_goals simp [BitVec.ult]

example (s : riscv_state) : «dfn'BGEU» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 999)) u.c_NextFetch}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BGEU», fixture, in32BitMode, curArch, architecture, MCSR, PC, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, branchTo, «write'NextFetch»]
  all_goals try rw [zero]
  all_goals simp [BitVec.ult]

example (s : riscv_state) : «dfn'BGEU» (0,0,4095) ({fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 1001 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 999)) u.c_NextFetch}) := by
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'BGEU», fixture, in32BitMode, curArch, architecture, MCSR, PC, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, branchTo, «write'NextFetch»]
  all_goals try rw [zero]
  all_goals simp [BitVec.ult]

end Flapjack.Test.L3ConditionalBranchParity
