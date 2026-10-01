import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack

/-- Full insertion-value equivalence on arbitrary sparse trees. HOL's unused
`n2` binder is omitted: it occurs in neither equality and has no guard or other
dependency in this source theorem. No well-formedness hypothesis is required. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "insert_eq"]
theorem insertEq {α : Type} (key : Nat) (v1 v2 : α) (tree : Spt α) :
    sptInsert key v1 tree = sptInsert key v2 tree ↔ v1 = v2 := by
  constructor
  · intro h
    have hlookup := congrArg (sptLookup key) h
    simpa only [sptLookup_sptInsert_same, Option.some.injEq] using hlookup
  · intro h
    cases h
    rfl

end Flapjack.Compiler.Backend.WordCse
