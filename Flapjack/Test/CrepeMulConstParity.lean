import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Semantics.CrepSem.HOLState
namespace Flapjack.Test.CrepeMulConstParity

-- Exact HOL evaluator replay of crep_arith_eval_mul_const_probe.out.
-- The source leaves every state field except locals arbitrary.
private def oracleState (state : CrepSemHOLState 64 Unit) : CrepSemHOLState 64 Unit :=
  { state with locals := HolFiniteMapExact.empty.update (2, .word 7) }

example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (oracleState state) (.var 2) = some (.word 7) := by
  simp [evalCrepSemHOLExp, oracleState, HolFiniteMapExact.update, FUPDATE]

example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (oracleState state) (crepMulConstHOL (.var 2) 0) = some (.word 0) := by
  simp [crepMulConstHOL, evalCrepSemHOLExp]

example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (oracleState state) (crepMulConstHOL (.var 2) 1) = some (.word 7) := by
  simp [crepMulConstHOL, evalCrepSemHOLExp, oracleState, HolFiniteMapExact.update, FUPDATE]

example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (oracleState state) (crepMulConstHOL (.var 2) 8) = some (.word 56) := by
  simp [crepMulConstHOL, crepDest2ExpHOL, evalCrepSemHOLExp, oracleState,
    HolFiniteMapExact.update, FUPDATE, wordShiftHOL]

example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (oracleState state) (crepMulConstHOL (.var 2) 3) = some (.word 21) := by
  simp [crepMulConstHOL, crepDest2ExpHOL, evalCrepSemHOLExp, oracleState,
    HolFiniteMapExact.update, FUPDATE, crepOpCrepWord]

end Flapjack.Test.CrepeMulConstParity
