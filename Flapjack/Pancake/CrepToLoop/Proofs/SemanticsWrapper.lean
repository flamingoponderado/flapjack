import Flapjack.HolRef

/-!
# crep_to_loop semantics-wrapper carriers

Exact ports of the carriers of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
semantics-wrapper section (4125-4397) (bead `flapjack-pxn.18.5.6.34`).
`semantics_wrapper_def` itself waits for a source-reviewed generic
`build_lprefix_lub` carrier (bead `flapjack-pxn.18.5.6.34.6`, blocked by
`flapjack-4ac.4.105.2`).
-/

namespace Flapjack

/-- Exact HOL `crep_to_loopProof$semantics_run_res`
    (`crep_to_loopProofScript.sml:4127-4130`):
    `semantics_run_res = RunError | CompleteResult 'a | Incomplete`.
    This is its own HOL type, declared afresh in `crep_to_loopProof`; it is not
    identified with the same-shaped `panProps$semantics_run_res`
    (`SemanticsRunResHOL`). Constructor order, arities and the single type
    parameter match HOL. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "semantics_run_res"]
inductive CrepToLoopSemanticsRunRes (α : Type u) where
  | RunError
  | CompleteResult (result : α)
  | Incomplete
  deriving DecidableEq, Repr

end Flapjack
