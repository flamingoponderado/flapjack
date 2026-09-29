import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.HolRef
import Flapjack.Misc.OptMmapCong

/-!
# crep_to_loopProof `crep_eval_upd_clock`

Counterpart of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`crep_eval_upd_clock` (3295, `[local]`) over the tagged exact crepSem eval
`evalCrepSemHOLExp` (bead `flapjack-pxn.18.5.6.33.10`).
-/

namespace Flapjack

namespace CrepToLoopCrepEvalFiniteSupport

/-- Same-module re-export of the canonical finite-support witness for the
    `CrepSemHOLState` carrier used by the qualified port below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {ffiState : Type} :
    (∀ (state : CrepSemBroadState width ffiState) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width ffiState,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end CrepToLoopCrepEvalFiniteSupport

theorem evalCrepSemHOLExp_upd_clock {width : Nat} [NeZero width] {ffiState : Type}
    (s : CrepSemHOLState width ffiState) (v : Nat) :
    ∀ e : CrepExpHOL width, evalCrepSemHOLExp { s with clock := v } e = evalCrepSemHOLExp s e
  | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by simp only [evalCrepSemHOLExp]
  | .load a | .load32 a | .loadByte a => by
      simp only [evalCrepSemHOLExp, evalCrepSemHOLExp_upd_clock s v a]
  | .op o args | .crepOp o args => by
      simp only [evalCrepSemHOLExp]
      rw [optMmapCongHOL args args _ _ rfl (fun x hx => evalCrepSemHOLExp_upd_clock s v x)]
  | .cmp o a b | .shift o a b => by
      simp only [evalCrepSemHOLExp, evalCrepSemHOLExp_upd_clock s v a,
        evalCrepSemHOLExp_upd_clock s v b]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepExpHOL.op.sizeOf_spec, CrepExpHOL.crepOp.sizeOf_spec];
       have := List.sizeOf_lt_of_mem hx; omega)

/-- Exact HOL `crep_eval_upd_clock` (`crep_to_loopProofScript.sml:3295-3296`, `[local]`):
    `crepSem$eval (s with clock := v) = crepSem$eval s`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "crep_eval_upd_clock"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem crep_eval_upd_clock {width : Nat} [NeZero width] {ffiState : Type}
    (s : CrepSemHOLState width ffiState) (v : Nat) :
    evalCrepSemHOLExp { s with clock := v } = evalCrepSemHOLExp s := by
  funext e
  exact evalCrepSemHOLExp_upd_clock s v e

end Flapjack
