import Flapjack.Test.CrepArithExactParity
import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.RiscV.PanMemory

namespace Flapjack.Test.CrepeSimpExpParity

/-! Exact carrier replay of the direct HOL `simp_exp` Var/Const EVAL rows. The
matching native `eval_def` preservation cases, including the proof-script-local
code-map update and full word_lab result, are kernel-checked in
`CrepArith.HOLStateMapc`. -/
example : crepSimpExpHOL (.var 7 : CrepExpHOL 8) = .var 7 := by
  simp [crepSimpExpHOL]

example (value : BitVec 8) :
    crepSimpExpHOL (.const value) = .const value := by
  simp [crepSimpExpHOL]

-- Additional 64-bit rows from `crep_simp_exp_probe.out`.
example : crepSimpExpHOL (.const (11 : BitVec 64)) = .const 11 := by
  simp [crepSimpExpHOL]
example : crepSimpExpHOL (.var 7 : CrepExpHOL 64) = .var 7 := by
  simp [crepSimpExpHOL]
#guard match crepSimpExpHOL (.crepOp .mul [.var 2, .const (8 : BitVec 64)]) with
  | .shift .lsl (.var 2) (.const 3) => true | _ => false

-- The HOL probe varies all fields except locals.
private def exactLocals (state : CrepSemHOLState 64 Unit) (value : BitVec 64) :
    CrepSemHOLState 64 Unit :=
  { state with locals := HolFiniteMapExact.empty.update (2, .word value) }

private def mulEight : CrepExpHOL 64 := .crepOp .mul [.var 2, .const 8]
private def nestedMul : CrepExpHOL 64 := .crepOp .mul [mulEight, .const 3]

example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 5) mulEight = some (.word 40) := by
  simp [evalCrepSemHOLExp, exactLocals, HolFiniteMapExact.update, FUPDATE,
    mulEight, crepOpCrepWord]
example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 5) (crepSimpExpHOL mulEight) = some (.word 40) := by
  simp [mulEight, Flapjack.Test.CrepArithExactParity.simpMul,
    crepSimpExpHOL, crepDestConstHOL, crepMulConstHOL, crepDest2ExpHOL, evalCrepSemHOLExp,
    exactLocals, HolFiniteMapExact.update, FUPDATE, mulEight, wordShiftHOL]

-- Preserve the earlier 7 * 8 and (7 * 8) * 3 evaluation checks.
example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 7) mulEight = some (.word 56) := by
  simp [evalCrepSemHOLExp, exactLocals, HolFiniteMapExact.update, FUPDATE,
    mulEight, crepOpCrepWord]
example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 7) (crepSimpExpHOL mulEight) = some (.word 56) := by
  simp [mulEight, Flapjack.Test.CrepArithExactParity.simpMul,
    crepSimpExpHOL, crepDestConstHOL, crepMulConstHOL, crepDest2ExpHOL, evalCrepSemHOLExp,
    exactLocals, HolFiniteMapExact.update, FUPDATE, mulEight, wordShiftHOL]
example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 7) nestedMul = some (.word 168) := by
  simp [evalCrepSemHOLExp, exactLocals, HolFiniteMapExact.update, FUPDATE,
    nestedMul, mulEight, crepOpCrepWord]
example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 7) (crepSimpExpHOL nestedMul) = some (.word 168) := by
  simp [mulEight, nestedMul, Flapjack.Test.CrepArithExactParity.simpMul,
    crepSimpExpHOL, crepDestConstHOL, crepMulConstHOL, crepDest2ExpHOL, evalCrepSemHOLExp,
    exactLocals, HolFiniteMapExact.update, FUPDATE, nestedMul, mulEight,
    wordShiftHOL, crepOpCrepWord]

end Flapjack.Test.CrepeSimpExpParity
