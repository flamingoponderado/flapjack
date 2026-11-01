import Flapjack.Compiler.Encoders.X64.Machine.ConstCase

/-!
# The `binop` register and immediate cases of `encoder_correct x64Target`

`arith (binop op r1 r2 (.reg r3))` lowers either to `mov r1, r3` (when `op = or`
and `r2 = r3`, so `r2 ||| r3 = r3`) or to `binopRR op r1 r3`.  `asm_ok` forces
`r1 = r2` in the latter case, so the register-register operation reads the same
two operands the source semantics does.  The immediate form lowers to
`monop not` for `xor -1` and to `binopRI op r i` otherwise.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- The instruction the register-register `binop` lowers to. -/
def x64BinopRRInsn (op : BinOp) (r1 r2 r3 : Nat) : X64Insn :=
  if op = .or && r2 = r3 then .movRR .z64 r1 r3 else .binopRR (x64Bop op) .z64 r1 r3

/-- The instruction the immediate `binop` lowers to. -/
def x64BinopRIImmInsn (op : BinOp) (r : Nat) (i : BitVec 64) : X64Insn :=
  if op = .xor && i = -1 then .monop .znot .z64 r else .binopRI (x64Bop op) .z64 r i

/-- `asm_ok` of a register-register `binop` splits into its register checks and
the two-register constraint. -/
theorem binopRR_ok (op : BinOp) (r1 r2 r3 : Nat)
    (h : asmOkExact (.inst (.arith (.binop op r1 r2 (.reg r3)))) x64Config = true) :
    (r1 = r2 ∨ op = .or ∧ r3 = r2) ∧
      asmRegOkExact r1 x64Config = true ∧
      asmRegOkExact r2 x64Config = true ∧ asmRegOkExact r3 x64Config = true := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, asmRegImmOkExact, x64Config,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.false_or] at h
  simp at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- `asm_ok` of an immediate `binop` splits into its register check and the
immediate-range check. -/
theorem binopRI_ok (op : BinOp) (r : Nat) (i : BitVec 64)
    (h : asmOkExact (.inst (.arith (.binop op r r (.imm i)))) x64Config = true) :
    asmRegOkExact r x64Config = true ∧
      ((((Sum.inl op : Sum BinOp Cmp) == (Sum.inl BinOp.xor : Sum BinOp Cmp)) = true ∧ i = -1) ∨
        (x64Min32.toInt ≤ i.toInt ∧ i.toInt ≤ x64Max32.toInt)) := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, asmRegImmOkExact, x64Config,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.false_or] at h
  simp at h
  exact h

/-- The `binop` value computed by the closed model is the source semantics'
`binop_upd` value. -/
theorem binopValue_x64Bop (op : BinOp) (a b : BitVec 64) :
    binopValue (x64Bop op) a b =
      (match op with
       | .add => a + b | .sub => a - b | .and => a &&& b | .or => a ||| b
       | .xor => a ^^^ b) := by
  cases op <;> rfl

/-- The `binop` value written by `binop_upd`. -/
theorem binopUpd_value (r : Nat) (op : BinOp) (a b : BitVec 64) (s : AsmState 64) :
    binopUpd r op a b s =
      updReg r (match op with
        | .add => a + b | .sub => a - b | .and => a &&& b | .or => a ||| b
        | .xor => a ^^^ b) s := by
  cases op <;> rfl

end Flapjack.Compiler.Encoders.X64
