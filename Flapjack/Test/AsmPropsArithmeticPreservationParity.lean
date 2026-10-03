import Flapjack.Compiler.Encoders.AsmProps.ArithmeticPreservation

/-! Original ASM invariant observations, including failed arithmetic writes. -/
namespace Flapjack.Test.AsmPropsArithmeticPreservationParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
private def fixture : AsmState 8 :=
  { regs := fun r => if r = 3 then 0 else 99, fpRegs := fun _ => 0,
    mem := fun _ => 9, memDomain := fun a => a = 0, pc := 7,
    lr := 5, align := 3, be := true, failed := false }
private def observe (op : HolArith 8) : Bool × Nat × Nat × Nat × Bool :=
  let t := arithUpd op fixture
  (t.failed, t.align, (t.mem 0).toNat, t.lr, t.be)
example : observe (.binop .add 0 2 (.imm 1)) = (false, 3, 9, 5, true) := by cbv
example : observe (.shift .lsl 0 2 (.reg 2)) = (true, 3, 9, 5, true) := by cbv
example : observe (.div 0 2 3) = (true, 3, 9, 5, true) := by cbv
example : observe (.longMul 0 1 2 2) = (false, 3, 9, 5, true) := by cbv
example : observe (.longDiv 0 1 2 2 3) = (true, 3, 9, 5, true) := by cbv
example : observe (.addCarry 0 2 2 4) = (false, 3, 9, 5, true) := by cbv
example : observe (.addOverflow 0 2 2 4) = (false, 3, 9, 5, true) := by cbv
example : observe (.subOverflow 0 2 2 4) = (false, 3, 9, 5, true) := by cbv
example (op : HolArith 8) : (arithUpd op fixture).memDomain 0 := by
  rw [(Flapjack.Compiler.Encoders.AsmProps.arithUpd_consts op fixture).1]
  rfl
example : (updPc 77 fixture).pc = 77 := by rfl
end Flapjack.Test.AsmPropsArithmeticPreservationParity
