module

public import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

@[expose] public section

namespace Flapjack.PanGlobalsCallHandlerFlag
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Synthesized evaluation proof step for compile_def's global Call handler
body, pan_globalsScript.sml:121-125. The full correctness proof uses this Seq
inline at pan_globalsProofScript.sml:1401-1450; no standalone HOL theorem has
this specialized statement, so it is untagged. An existing word-valued flag
suffices for validity; no successful assignment or target simulation is assumed. -/
theorem handlerFlagNormal {width : Nat} {σ : Type} [NeZero width]
    (state post : PanSemStateFiniteExact width σ) (handler : ProgHOL width)
    (flag : MlS) (oldFlag : BitVec width)
    (run : evaluateHOLFiniteState state handler = (none, post))
    (binding : post.locals.lookup flag = some (.val (.word oldFlag))) :
    evaluateHOLFiniteState state
      (.seq handler (.assign .local flag (.const (BitVec.ofNat width 1)))) =
      (none, setVarHOLFinite flag (.val (.word (BitVec.ofNat width 1))) post) := by
  classical
  rw [evaluateHOLFiniteState_seq_line780, run]
  simp only
  rw [evaluateHOLFiniteState_assign]
  simp [evalHOLExact, isValidValueHOLFinite, lookupKvarHOLFinite, binding,
    shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]

end Flapjack.PanGlobalsCallHandlerFlag
