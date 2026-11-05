import Flapjack.Pancake.Proofs.CrepInline.UnreachElimProgSize
import Mathlib.SetTheory.Cardinal.Finite

namespace Flapjack.CrepInlineUnreachElimProgSize

open Flapjack.CrepLangGeneratedSize

/-- Flapjack-only descriptor for reviewing the missing bare index translation.
It retains the index type itself. On nonempty finite types it is their cardinal;
on infinite types it is one, matching the branches inspected in original
HOL fcpScript.sml:63-65 (pinned under hol4/src/n-bit). No HOL tag: the
combined index/word translation still awaits source and qualifier review. -/
noncomputable def holIndexDimension (α : Type) : Nat := max 1 (Nat.card α)

instance holIndexDimension_neZero (α : Type) : NeZero (holIndexDimension α) :=
  ⟨by unfold holIndexDimension; omega⟩

end Flapjack.CrepInlineUnreachElimProgSize
