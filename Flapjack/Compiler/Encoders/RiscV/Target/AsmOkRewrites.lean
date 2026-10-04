import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Mathlib.Tactic.Tauto
namespace Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack Compiler.Encoders.Asm
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
/-- Canonical Sum equality reduction; untagged local composition infrastructure. -/
private theorem inl_xor (b : BinOp) :
    ((Sum.inl b : Sum BinOp Cmp) == Sum.inl .xor) = (b == .xor) := by
  cases b <;> rfl
/-- Canonical disjoint Sum constructors; no separately named HOL original. -/
private theorem inr_xor (x : Cmp) :
    ((Sum.inr x : Sum BinOp Cmp) == Sum.inl .xor) = false := rfl
attribute [local simp] inl_xor inr_xor BitVec.slt_eq_decide BitVec.sle_eq_decide
  decide_eq_true_iff Bool.and_eq_true and_assoc Nat.mod_one
/-- Complete generated original per-form asm_ok bundle: all 41 conjuncts in
source order, all original free variables universally bound, fixed word64,
exact asm carriers and current reviewed riscvConfig. HOL word comparisons are
signed toInt comparisons; the strict Sub lower bound, XOR -1 exception,
zero-shift restriction, visible-register exclusions and all source-permitted
aliases are retained. All eight memory and sixteen rejected FP forms appear.
`r` is HOL numeric r-prime after GEN_ALL; callTarget is HOL word-valued r.
No subset, execution/output premise or alternative configuration is assumed. -/
theorem riscvAsmOkRewrites (r r1 r2 r3 r4 r5 : Nat)
    (w i callTarget : BitVec 64) (b : BinOp) (s : Shift)
    (n : HolRegImm 64) (x : Cmp) :
    (asmOkExact (.inst .skip) riscvConfig = true ↔ True) ∧
    (asmOkExact (.inst (.const r w)) riscvConfig = true ↔ (r < 32 ∧ r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 31)) ∧
    (asmOkExact (.inst (.arith (.binop b r1 r2 (.reg r3)))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (r3 < 32 ∧ r3 ≠ 0 ∧ r3 ≠ 2 ∧ r3 ≠ 3 ∧ r3 ≠ 4 ∧ r3 ≠ 31)) ∧
    (asmOkExact (.inst (.arith (.binop b r1 r2 (.imm w)))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ ((b = .xor ∧ w = -1) ∨ (if b = .sub then (-2048 : BitVec 64).toInt < w.toInt else (-2048 : BitVec 64).toInt ≤ w.toInt) ∧ w.toInt ≤ (2047 : BitVec 64).toInt)) ∧
    (asmOkExact (.inst (.arith (.shift s r1 r2 n))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (match n with | .reg r => (r < 32 ∧ r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 31) | .imm i => (i = 0 → s = .lsl) ∧ i.toNat < 64)) ∧
    (asmOkExact (.inst (.arith (.div r1 r2 r3))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (r3 < 32 ∧ r3 ≠ 0 ∧ r3 ≠ 2 ∧ r3 ≠ 3 ∧ r3 ≠ 4 ∧ r3 ≠ 31)) ∧
    (asmOkExact (.inst (.arith (.longMul r1 r2 r3 r4))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (r3 < 32 ∧ r3 ≠ 0 ∧ r3 ≠ 2 ∧ r3 ≠ 3 ∧ r3 ≠ 4 ∧ r3 ≠ 31) ∧ (r4 < 32 ∧ r4 ≠ 0 ∧ r4 ≠ 2 ∧ r4 ≠ 3 ∧ r4 ≠ 4 ∧ r4 ≠ 31) ∧ r1 ≠ r3 ∧ r1 ≠ r4) ∧
    (asmOkExact (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) riscvConfig = true ↔ False) ∧
    (asmOkExact (.inst (.arith (.addCarry r1 r2 r3 r4))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (r3 < 32 ∧ r3 ≠ 0 ∧ r3 ≠ 2 ∧ r3 ≠ 3 ∧ r3 ≠ 4 ∧ r3 ≠ 31) ∧ (r4 < 32 ∧ r4 ≠ 0 ∧ r4 ≠ 2 ∧ r4 ≠ 3 ∧ r4 ≠ 4 ∧ r4 ≠ 31) ∧ r1 ≠ r3 ∧ r1 ≠ r4) ∧
    (asmOkExact (.inst (.arith (.addOverflow r1 r2 r3 r4))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (r3 < 32 ∧ r3 ≠ 0 ∧ r3 ≠ 2 ∧ r3 ≠ 3 ∧ r3 ≠ 4 ∧ r3 ≠ 31) ∧ (r4 < 32 ∧ r4 ≠ 0 ∧ r4 ≠ 2 ∧ r4 ≠ 3 ∧ r4 ≠ 4 ∧ r4 ≠ 31) ∧ r1 ≠ r3) ∧
    (asmOkExact (.inst (.arith (.subOverflow r1 r2 r3 r4))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (r3 < 32 ∧ r3 ≠ 0 ∧ r3 ≠ 2 ∧ r3 ≠ 3 ∧ r3 ≠ 4 ∧ r3 ≠ 31) ∧ (r4 < 32 ∧ r4 ≠ 0 ∧ r4 ≠ 2 ∧ r4 ≠ 3 ∧ r4 ≠ 4 ∧ r4 ≠ 31) ∧ r1 ≠ r3) ∧
    (asmOkExact (.inst (.mem .load r1 (.addr r2 w))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (-2048 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (2047 : BitVec 64).toInt) ∧
    (asmOkExact (.inst (.mem .load8 r1 (.addr r2 w))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (-2048 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (2047 : BitVec 64).toInt) ∧
    (asmOkExact (.inst (.mem .load16 r1 (.addr r2 w))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (-2048 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (2047 : BitVec 64).toInt) ∧
    (asmOkExact (.inst (.mem .load32 r1 (.addr r2 w))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (-2048 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (2047 : BitVec 64).toInt) ∧
    (asmOkExact (.inst (.mem .store r1 (.addr r2 w))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (-2048 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (2047 : BitVec 64).toInt) ∧
    (asmOkExact (.inst (.mem .store8 r1 (.addr r2 w))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (-2048 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (2047 : BitVec 64).toInt) ∧
    (asmOkExact (.inst (.mem .store16 r1 (.addr r2 w))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (-2048 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (2047 : BitVec 64).toInt) ∧
    (asmOkExact (.inst (.mem .store32 r1 (.addr r2 w))) riscvConfig = true ↔ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31) ∧ (-2048 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (2047 : BitVec 64).toInt) ∧
    (asmOkExact (.jump w) riscvConfig = true ↔ (-2147483648 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (0x7FFFF7FF : BitVec 64).toInt ∧ asmAligned 2 w = true) ∧
    (asmOkExact (.jumpCmp x r1 (.reg r2) w) riscvConfig = true ↔ ((-1048576+8 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (1048575+4 : BitVec 64).toInt ∧ asmAligned 2 w = true) ∧ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (r2 < 32 ∧ r2 ≠ 0 ∧ r2 ≠ 2 ∧ r2 ≠ 3 ∧ r2 ≠ 4 ∧ r2 ≠ 31)) ∧
    (asmOkExact (.jumpCmp x r1 (.imm i) w) riscvConfig = true ↔ ((-1048576+8 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (1048575+4 : BitVec 64).toInt ∧ asmAligned 2 w = true) ∧ (r1 < 32 ∧ r1 ≠ 0 ∧ r1 ≠ 2 ∧ r1 ≠ 3 ∧ r1 ≠ 4 ∧ r1 ≠ 31) ∧ (-2048 : BitVec 64).toInt ≤ i.toInt ∧ i.toInt ≤ (2047 : BitVec 64).toInt) ∧
    (asmOkExact (.call callTarget) riscvConfig = true ↔ (-2147483648 : BitVec 64).toInt ≤ callTarget.toInt ∧ callTarget.toInt ≤ (0x7FFFF7FF : BitVec 64).toInt ∧ asmAligned 2 callTarget = true) ∧
    (asmOkExact (.jumpReg r) riscvConfig = true ↔ (r < 32 ∧ r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 31)) ∧
    (asmOkExact (.loc r w) riscvConfig = true ↔ (r < 32 ∧ r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 31) ∧ (-2147483648 : BitVec 64).toInt ≤ w.toInt ∧ w.toInt ≤ (0x7FFFF7FF : BitVec 64).toInt ∧ asmAligned 2 w = true) := by
  cases b <;> cases n
  all_goals
    simp [asmOkExact,asmInstOkExact,asmArithOkExact,asmRegImmOkExact,
      asmRegOkExact,asmCmpOkExact,
      asmAddrOffsetOkExact,asmHwOffsetOkExact,asmByteOffsetOkExact,
      asmJumpOffsetOkExact,asmCjumpOffsetOkExact,asmLocOffsetOkExact,
      asmOffsetOkExact,asmAligned,riscvConfig,BitVec.slt_eq_decide,
      BitVec.sle_eq_decide,Bool.and_eq_true,and_assoc]
    dsimp +instances only [riscvConfig]
    simp
  all_goals tauto
end Flapjack.Compiler.Encoders.RiscV.Target
