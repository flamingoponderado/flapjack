module

public import Flapjack.Misc.SetSep.Top
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack

/-- Forget the right-hand separated assertion while retaining the left frame. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "STAR_fun2set_IMP_SEP_T"]
theorem starFun2SetImpSepT {α β : Type} (p q : ((α × β) → Prop) → Prop)
    (m : α → β) (dm : α → Prop)
    (h : SetSep.star p q (SetSep.fun2Set (m, dm))) :
    SetSep.star p SetSep.sepT (SetSep.fun2Set (m, dm)) := by
  obtain ⟨left, right, split, hp, hq⟩ := h
  exact ⟨left, right, split, hp, True.intro⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
