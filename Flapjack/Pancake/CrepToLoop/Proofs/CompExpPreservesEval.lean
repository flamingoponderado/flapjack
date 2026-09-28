import Flapjack.Pancake.CrepToLoop.Proofs.CrepEvalHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.LoopEvaluateHelpers

/-!
# crep_to_loop expression simulation

Proof-side infrastructure for the `comp_exp_preserves_eval` Op case in
`cakeml/pancake/proofs/crep_to_loopProofScript.sml` (bead
`flapjack-pxn.18.5.6.33.15.6`).  The case itself is not ported in this file
yet.  The helpers below expose the exact HOL evaluator clauses over their
already tagged Crep and Loop carriers so the argument-list induction can be
stated without substituting a simplified evaluator.  These clause projections
are Flapjack-only infrastructure and do not claim a separate HOL theorem.
-/

namespace Flapjack

open Classical

variable {width : Nat} [NeZero width] {ffiState : Type}

/-- Flapjack-only projection of the exact Crep `eval_def` Op clause. The
    namespace-local classical instance supplies `DecidablePred state.memaddrs`
    when elaborating the evaluator call; it is not a proposition premise in
    this theorem's interface and changes neither the evaluator nor production. -/
theorem evalCrepSemHOLExp_op_clause (state : CrepSemHOLState width ffiState)
    (operator : BinOp)
    (expressions : List (CrepExpHOL width)) (values : List (BitVec width))
    (hvalues : expressions.mapM (evalCrepSemHOLExp state) =
      some (values.map HolWordLab.word)) :
    evalCrepSemHOLExp state (.op operator expressions) =
      (wordOpHOL operator values).map HolWordLab.word := by
  simp [evalCrepSemHOLExp, hvalues, Function.comp_def]

/-- Flapjack-only projection of the exact Loop `eval_def` Op clause. -/
theorem loopEvalHOLExact_op_clause {F : Type}
    (state : LoopSemStateFiniteExact width F) (operator : BinOp)
    (expressions : List (HolLoopExp width)) (values : List (BitVec width))
    (hvalues : theWords (expressions.map (LoopSemStateFiniteExact.eval state)) =
      some values) :
    LoopSemStateFiniteExact.eval state (.op operator expressions) =
      (wordOpHOL operator values).map WordLocW.word := by
  simp [LoopSemStateFiniteExact.eval, hvalues]

end Flapjack
