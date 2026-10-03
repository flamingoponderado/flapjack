import Flapjack.Compiler.Backend.LabToTarget.MmioShmem

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack
private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩

/-- Full original successful optional-boundary classification. The original
length bound makes every prefix EL in range; each suffix EL retains its own
source bound. The optional-choice definition and past-end defaults are unchanged. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "mmio_pcs_min_index_is_SOME"]
theorem mmioPcsMinIndex_isSome (names : List HolFfiName) (index : Nat) :
    mmioPcsMinIndex names = some index →
    index ≤ names.length ∧
      (∀ j, j < index → ∃ name, holEl j names = .extCall name) ∧
      (∀ j, index ≤ j ∧ j < names.length →
        ∃ operation, holEl j names = .sharedMem operation) := by
  classical
  intro hs
  have hb : mmioIndexBoundary names index := by
    unfold mmioPcsMinIndex at hs
    split at hs
    · next h =>
        have hi : Classical.choose h = index := Option.some.inj hs
        simpa only [hi] using Classical.choose_spec h
    · cases hs
  exact ⟨hb.1, hb.2.1, fun j hj => hb.2.2 j hj.1 hj.2⟩

end Flapjack.Compiler.Backend.LabToTarget
