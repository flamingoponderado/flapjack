module

public import Flapjack.Compiler.Backend.BvlHandle

@[expose] public section

/-! The source sequence recognizer's exact matching condition. -/
namespace Flapjack.Compiler.Backend.BvlHandle

/-- Sequence recognition succeeds exactly for the source's two-let pattern. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "dest_Seq_thm"]
theorem destSeq_iff (x y : Bvl.Exp) :
    ∀ e, destSeq e = some (x, y) ↔ e = .let [x, y] (.var 1) := by
  intro e
  cases e <;> simp only [destSeq, reduceCtorEq]
  all_goals repeat' split <;> simp_all
  all_goals intro h; apply_assumption; exact h

end Flapjack.Compiler.Backend.BvlHandle
