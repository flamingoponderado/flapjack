import Flapjack.Compiler.Backend.Semantics.ClosSem.GeneratedSize
import Mathlib.Tactic

namespace Flapjack.Compiler.Backend.ClosCall
open ClosSem

/-- A value occurring in an environment has smaller generated HOL size. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_size_lemma"]
theorem valueSize_mem (v : Value) (vl : List Value) (h : v ∈ vl) :
    valueSizeHOL v < valueListSizeHOL vl := by
  induction vl with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [valueListSizeHOL]
    rcases h with rfl | h
    · omega
    · have bound := ih h
      omega
end Flapjack.Compiler.Backend.ClosCall
