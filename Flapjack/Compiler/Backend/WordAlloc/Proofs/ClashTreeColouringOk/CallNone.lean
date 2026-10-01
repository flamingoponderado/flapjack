import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Motive

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc

/-- HOL `clash_tree_colouring_ok`, the Call with no return branch. The source
ignores any exception handler here; its program and labels remain arbitrary.
All six motive premises and all five conclusions are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_CallNone {width : Nat} [NeZero width]
    (target : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    clashTreeGoal (.call none target args handler : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, -, hi, hc⟩
  have checked : checkCol f (numsetListInsert args .ln) = some (livein, flivein) := by
    simpa only [getClashTree, checkClashTree] using hc
  obtain ⟨equal, injective, image⟩ := checkColInj f _ livein flivein checked
  subst livein
  refine ⟨sptWf_numsetListInsert .ln (by rfl) args, injective, ?_, by rw [getLive], image⟩
  simpa only [colouringOk, getLive, getWrites, sptUnion] using And.intro injective hi

end Flapjack.WordAlloc
