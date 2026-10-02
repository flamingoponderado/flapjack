import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClock

namespace Flapjack

/-- Two completed native machine runs have the same full result regardless of
clock. This local HOL lemma uses only the two original non-TimeOut runs. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "evaluate_ignore_clocks"
  (words_as_type_indexed_bitvec)]
theorem evaluateTargetIgnoreClocks {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (mc : MachineConfig width state projection)
    (ffi : HolFfiState σ) (k k' : Nat) (ms : state)
    (r1 r2 : MachineResult) (ms1 ms2 : state) (st1 st2 : HolFfiState σ)
    (h : evaluateTargetHOL mc ffi k ms = (r1, ms1, st1) ∧ r1 ≠ .timeOut ∧
      evaluateTargetHOL mc ffi k' ms = (r2, ms2, st2) ∧ r2 ≠ .timeOut) :
    (r1, ms1, st1) = (r2, ms2, st2) := by
  have h1 := evaluateTargetAddClock mc ffi k ms k' r1 ms1 st1 h.1 h.2.1
  have h2 := evaluateTargetAddClock mc ffi k' ms k r2 ms2 st2 h.2.2.1 h.2.2.2
  exact h1.symm.trans (by simpa only [Nat.add_comm] using h2)

end Flapjack
