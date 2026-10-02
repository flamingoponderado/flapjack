import Flapjack.Compiler.Backend.Semantics.WordSem.Env
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack

open Flapjack

/-- Full original comparator transitivity. The reviewed native comparator
uses signed word order, Word before Loc, and descending location coordinates. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "transitive_key_val_compare"
  (words_as_type_indexed_bitvec)]
theorem transitiveKeyValCompare {width : Nat} [NeZero width]
    (x y z : Nat × WordLocW width)
    (hxy : wordSemKeyValCompare x y = true)
    (hyz : wordSemKeyValCompare y z = true) :
    wordSemKeyValCompare x z = true := by
  rcases x with ⟨a, x⟩
  rcases y with ⟨b, y⟩
  rcases z with ⟨c, z⟩
  cases x <;> cases y <;> cases z <;>
    simp_all [wordSemKeyValCompare, BitVec.sle] <;> omega

/-- Full original comparator totality, including equality and both directions
of signed word comparison, with no key uniqueness or constructor restriction. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "total_key_val_compare"
  (words_as_type_indexed_bitvec)]
theorem totalKeyValCompare {width : Nat} [NeZero width]
    (x y : Nat × WordLocW width) :
    wordSemKeyValCompare x y = true ∨ wordSemKeyValCompare y x = true := by
  rcases x with ⟨a, x⟩
  rcases y with ⟨b, y⟩
  cases x <;> cases y <;> simp [wordSemKeyValCompare, BitVec.sle] <;> omega

end Flapjack.Compiler.Backend.WordToStack
