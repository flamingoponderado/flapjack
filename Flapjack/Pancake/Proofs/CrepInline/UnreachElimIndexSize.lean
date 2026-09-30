import Flapjack.Pancake.Proofs.CrepInline.UnreachElimProgSize
import Mathlib.SetTheory.Cardinal.Finite

namespace Flapjack.CrepInlineUnreachElimProgSize

open Flapjack.CrepLangGeneratedSize

/-- Flapjack-only descriptor for reviewing the missing bare index translation.
It retains the index type itself. On nonempty finite types it is their cardinal;
on infinite types it is one, matching the branches inspected in original
HOL fcpScript.sml:63-65. No HOL tag: the source-library declaration is not pinned
in the reference catalogue and the combined index/word translation awaits review. -/
noncomputable def holIndexDimension (α : Type) : Nat := max 1 (Nat.card α)

instance holIndexDimension_neZero (α : Type) : NeZero (holIndexDimension α) :=
  ⟨by unfold holIndexDimension; omega⟩

/-- Flapjack infrastructure checking the finite branch of the descriptor. -/
theorem holIndexDimension_finite (α : Type) [Nonempty α] [Finite α] :
    holIndexDimension α = Nat.card α := by
  exact max_eq_right (Nat.card_pos (α := α))

/-- Flapjack infrastructure checking the infinite branch; the index type is
not replaced by the finite word carrier. -/
theorem holIndexDimension_infinite (α : Type) [Infinite α] :
    holIndexDimension α = 1 := by
  simp [holIndexDimension]

/-- Flapjack candidate retaining the size function domain as the SAME bare index
whose dimension determines both program word widths. This adds no independent
width or type quantifier. No HOL tag until the index/word translation rule and
source-library dimension descriptor are reviewed under bead .18.5.5.50. -/
theorem unreachElimProgSize_indexed {α : Type} [Nonempty α]
    (p q : CrepProgHOL (holIndexDimension α)) (r : Option CrepEarlyExitHOL)
    (f : α → Nat) (h : unreachElimHOLExact p = (q, r)) :
    crepProgSizeHOL f q ≤ crepProgSizeHOL f p :=
  unreachElimProgSize p q r f h

end Flapjack.CrepInlineUnreachElimProgSize
