module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Flapjack.Basis.Pure.MlList.SortPerm
public import Lean.Elab.Tactic.Omega

@[expose] public section

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

/-- Exact HOL `SORTS_SORT_key_val_compare`
(`word_to_stackProofScript.sml:1251-1257`): the CakeML list sort sorts by the
key/value comparator. HOL derives it from `sort_SORTS` and the comparator's
transitivity and totality. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SORTS_SORT_key_val_compare"
  (words_as_type_indexed_bitvec)]
theorem sortsSortKeyValCompare {width : Nat} [NeZero width] :
    holSorts
      (Basis.Pure.MlList.sort :
        (Nat × WordLocW width → Nat × WordLocW width → Bool) →
          List (Nat × WordLocW width) → List (Nat × WordLocW width))
      wordSemKeyValCompare := by
  refine Basis.Pure.MlList.sortSorts (α := Nat × WordLocW width) wordSemKeyValCompare ⟨?_, ?_⟩
  · intro x y z h
    exact transitiveKeyValCompare x y z h.1 h.2
  · intro x y
    exact totalKeyValCompare x y

end Flapjack.Compiler.Backend.WordToStack
