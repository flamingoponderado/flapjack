import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Complete original loop-table validity predicate. HOL EVERY is the ordinary
pointwise list predicate; INJ into UNIV is precisely the domain-restricted
injectivity implication. The entry and exit name-set payload types are
independently arbitrary, rather than restricted to the Unit instance used by
ssaCcTrans. This is a proof predicate with no executed compiler route. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "lt_ok_def"]
def ltOK {α β : Type} (tables : List (Spt Nat × Spt α × Spt β)) : Prop :=
  ∀ table, table ∈ tables →
    (∀ x y, sptDomain table.2.1 x → sptDomain table.2.1 y →
      optionLookup table.1 x = optionLookup table.1 y → x = y) ∧
    (∀ x y, sptDomain table.2.2 x → sptDomain table.2.2 y →
      optionLookup table.1 x = optionLookup table.1 y → x = y)

end Flapjack.Compiler.Backend.WordAlloc
