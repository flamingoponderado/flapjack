module

public import Flapjack.HolRef

@[expose] public section

/-! backendProofScript.sml 2709-2711: `is_64_bits_def`, the word-size test
used by the space-safety predicate `is_safe_for_space`. -/
namespace Flapjack.Compiler.Backend.BackendProof

/-- Exact HOL `backendProof$is_64_bits_def` (`backendProofScript.sml:2709-2711`):
`is_64_bits (:'a) ⇔ dimindex (:'a) = 64`. HOL's word dimension is used only
numerically, as the named positive width; the Bool result is decided. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "is_64_bits_def"
  (word_dimension_as_width := width)]
def is64Bits (width : Nat) [NeZero width] : Bool := decide (width = 64)

end Flapjack.Compiler.Backend.BackendProof
