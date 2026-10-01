import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full native bound-monotonicity result, with only the original conjunction
of map validity and counter ordering as its premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_more"]
theorem ssaMapOKMore (next : Nat) (ssa : Spt Nat) (nextOut : Nat) :
    ssaMapOK next ssa ∧ next ≤ nextOut → ssaMapOK nextOut ssa := by
  rintro ⟨valid, bound⟩ key value found
  have original := valid key value found
  exact ⟨original.1, Nat.lt_of_lt_of_le original.2 bound⟩

end Flapjack.Compiler.Backend.WordAlloc
