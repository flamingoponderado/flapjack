import Flapjack.Compiler.Backend.WordAlloc.HeuCounters
import Flapjack.Pancake.WordLang

namespace Flapjack.WordAlloc

/-- Literal instruction heuristic counter collection. Constructor positions
and nested update order follow the source, including aliased registers.
Memory addresses are ignored. FP moves count both integer registers at every
width; this differs from the width-sensitive clash-tree instruction analysis.
Unlisted memory widths and FP operations retain the entire input tree.
The executed allocator migration remains a separate dependency. -/
-- riscv-mi: integer-only specialization of the referenced HOL declaration.

def getHeuInst {width : Nat} [NeZero width] :
    WordLangInst (BitVec width) → Spt HeuData → Spt HeuData
  | .skip, t => t
  | .const r _, t => add1LhsConst r t
  | .arith (.binop _ r1 r2 (.reg r3)), t =>
      add1LhsReg r1 (add1RhsReg r3 (add1RhsReg r2 t))
  | .arith (.binop _ r1 r2 (.imm _)), t => add1LhsReg r1 (add1RhsReg r2 t)
  | .arith (.shift _ r1 r2 (.reg r3)), t =>
      add1LhsReg r1 (add1RhsReg r3 (add1RhsReg r2 t))
  | .arith (.shift _ r1 r2 (.imm _)), t => add1LhsReg r1 (add1RhsReg r2 t)
  | .arith (.div r1 r2 r3), t => add1LhsReg r1 (add1RhsReg r3 (add1RhsReg r2 t))
  | .arith (.addCarry r1 r2 r3 r4), t =>
      add1LhsReg r4 (add1LhsReg r1 (add1RhsReg r4 (add1RhsReg r3 (add1RhsReg r2 t))))
  | .arith (.addOverflow r1 r2 r3 r4), t =>
      add1LhsReg r4 (add1LhsReg r1 (add1RhsReg r3 (add1RhsReg r2 t)))
  | .arith (.subOverflow r1 r2 r3 r4), t =>
      add1LhsReg r4 (add1LhsReg r1 (add1RhsReg r3 (add1RhsReg r2 t)))
  | .arith (.longMul r1 r2 r3 r4), t =>
      add1LhsReg r2 (add1LhsReg r1 (add1RhsReg r4 (add1RhsReg r3 t)))
  | .arith (.longDiv r1 r2 r3 r4 r5), t =>
      add1LhsReg r2 (add1LhsReg r1 (add1RhsReg r5 (add1RhsReg r4 (add1RhsReg r3 t))))
  | .mem .load r (.addr _ _), t => add1LhsMem r t
  | .mem .store r (.addr _ _), t => add1RhsMem r t
  | .mem .load32 r (.addr _ _), t => add1LhsMem r t
  | .mem .load8 r (.addr _ _), t => add1LhsMem r t
  | .mem .store32 r (.addr _ _), t => add1RhsMem r t
  | .mem .store8 r (.addr _ _), t => add1RhsMem r t
  | _, t => t

end Flapjack.WordAlloc
