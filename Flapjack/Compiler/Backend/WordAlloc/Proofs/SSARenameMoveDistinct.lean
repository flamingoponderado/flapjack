import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameLookup
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.ListNextVarRenameArithmetic

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full original scoped injection result for actual list-renaming Move.
All five original conjuncts remain: producer equation, distinct input names,
two input memberships and equal output-map selectors. No global injection,
map validity, register allocation or target execution is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_move_distinct"
  (words_as_type_indexed_bitvec)]
theorem listNextVarRenameMoveDistinct {width : Nat} [NeZero width]
    (ssa : Spt Nat) (next : Nat) (names : List Nat)
    (move : WordLangProgHOL (BitVec width)) (mapOut : Spt Nat) (nextOut x y : Nat)
    (h : listNextVarRenameMove ssa next names = (move,mapOut,nextOut) ∧
      names.Nodup ∧ x ∈ names ∧ y ∈ names ∧
      optionLookup mapOut x = optionLookup mapOut y) : x = y := by
  generalize renamed : listNextVarRename names ssa next = result
  rcases result with ⟨outputs,tree,counter⟩
  have produced := h.1
  simp only [listNextVarRenameMove,renamed,Prod.mk.injEq] at produced
  rcases produced with ⟨_,rfl,rfl⟩
  have distinct := listNextVarRenameLemma1 names ssa next outputs tree counter renamed
  have lookup := listNextVarRenameLemma2Prime names ssa next outputs tree counter renamed h.2.1
  have outputDistinct : (names.map (optionLookup tree)).Nodup := by
    rw [lookup.1] at distinct
    have selectors : optionLookup tree = (fun key => (sptLookup key tree).getD 0) := by
      funext key
      unfold optionLookup
      cases sptLookup key tree <;> rfl
    rw [selectors]
    exact distinct.1
  exact (List.nodup_map_iff_inj_on h.2.1).mp outputDistinct x h.2.2.1 y h.2.2.2.1 h.2.2.2.2

end Flapjack.Compiler.Backend.WordAlloc
