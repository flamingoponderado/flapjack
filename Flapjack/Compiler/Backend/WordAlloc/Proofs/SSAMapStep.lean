import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds

namespace Flapjack.Compiler.Backend.WordAlloc

/-- The full original counter-step lemma, derived from the accepted native
bound-monotonicity theorem without any extra map or counter premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_lem"]
theorem ssaMapOKLem (next : Nat) (ssa : Spt Nat) :
    ssaMapOK next ssa → ssaMapOK (next + 2) ssa := by
  intro valid
  exact ssaMapOKMore next ssa (next + 2) ⟨valid, Nat.le_add_right next 2⟩

end Flapjack.Compiler.Backend.WordAlloc
