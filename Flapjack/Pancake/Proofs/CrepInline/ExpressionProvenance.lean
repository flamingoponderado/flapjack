import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.CrepInline.Canonical

namespace Flapjack

/-- Original nested-declaration expression provenance, including mismatched
name/value lengths. No matching-length guard is added. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_nested_decs"
  (words_as_type_indexed_bitvec)]
theorem crepInline_expsOfNestedDecs {width : Nat} [NeZero width]
    (e : CrepExpHOL width) (vs : List Nat) (es : List (CrepExpHOL width))
    (p : CrepProgHOL width)
    (member : e ∈ crepExpsOfHOL (nestedDecsHOL vs es p)) :
    e ∈ es ∨ e ∈ crepExpsOfHOL p := by
  induction vs generalizing es with
  | nil =>
      cases es <;> simp_all [nestedDecsHOL, crepExpsOfHOL]
  | cons v vs ih =>
      cases es with
      | nil => simp [nestedDecsHOL, crepExpsOfHOL] at member
      | cons a es =>
          simp only [nestedDecsHOL, crepExpsOfHOL, List.mem_cons] at member
          rcases member with same | tail
          · exact Or.inl (List.mem_cons.mpr (Or.inl same))
          · rcases ih es tail with h | h
            · exact Or.inl (List.mem_cons.mpr (Or.inr h))
            · exact Or.inr h

end Flapjack
