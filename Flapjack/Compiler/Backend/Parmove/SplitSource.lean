import Flapjack.Compiler.Backend.Parmove

namespace Flapjack.Compiler.Backend.Parmove

/-! Flapjack-only proof infrastructure for the actual index-independent source
search used by fstep. HOL fstep_dstep derives these facts from splitAtPki's
least matching index; these helpers have no separately named HOL original and
are not ports of the general indexed list combinator. No search certificate
is assumed: both facts follow from the actual recursive splitSource. -/

theorem splitSource_prefix_noRead {α : Type} [DecidableEq α]
    (destination : Option α) (moves : List (Move α)) :
    destination ∉ (splitSource destination moves).1.map Prod.snd := by
  induction moves with
  | nil => simp [splitSource]
  | cons move moves ih =>
      by_cases same : move.2 = destination
      · simp [splitSource, same]
      · simpa [splitSource, same] using And.intro (Ne.symm same) ih

theorem splitSource_suffix_match {α : Type} [DecidableEq α]
    (destination : Option α) (moves : List (Move α))
    (head : Move α) (tail : List (Move α)) :
    (splitSource destination moves).2 = head :: tail → head.2 = destination := by
  induction moves with
  | nil => simp [splitSource]
  | cons move moves ih =>
      intro found
      by_cases same : move.2 = destination
      · have equal : move = head := by
          simpa [splitSource, same] using congrArg List.head? found
        exact equal ▸ same
      · apply ih
        simpa [splitSource, same] using found

/-- Empty suffix is equivalent to absence of a matching read in the entire
input. This is derived from the real partition and first-match laws. -/
theorem splitSource_suffix_nil_iff {α : Type} [DecidableEq α]
    (destination : Option α) (moves : List (Move α)) :
    (splitSource destination moves).2 = [] ↔ destination ∉ moves.map Prod.snd := by
  constructor
  · intro empty
    have partition := splitSource_append destination moves
    rw [empty, List.append_nil] at partition
    rw [← partition]
    exact splitSource_prefix_noRead destination moves
  · intro noRead
    cases found : (splitSource destination moves).2 with
    | nil => rfl
    | cons head tail =>
        have source := splitSource_suffix_match destination moves head tail found
        have member : head ∈ moves := by
          rw [← splitSource_append destination moves]
          simp [found]
        exact False.elim (noRead (List.mem_map.mpr ⟨head, member, source⟩))

end Flapjack.Compiler.Backend.Parmove
