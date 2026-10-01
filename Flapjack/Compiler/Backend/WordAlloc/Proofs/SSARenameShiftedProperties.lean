import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenamePropertyWrappers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARegisterFlip
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapStep

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full original derived shifted raw-list theorem. It retains the map bound
at the shifted input counter, stack-before-allocation disjunction/implications,
and the original derived quantifier order confirmed by literal HOL replay. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_props_2"]
theorem listNextVarRenameProps2 (names : List Nat) (ssa : Spt Nat) (next : Nat)
    (ssaOut : Spt Nat) (nextOut : Nat) (namesOut : List Nat)
    (produced : listNextVarRename names ssa (next + 2) = (namesOut, ssaOut, nextOut))
    (h : (isStackVar next ∨ isAllocVar next) ∧ ssaMapOK (next + 2) ssa) :
    next + 2 ≤ nextOut ∧ (isStackVar next → isAllocVar nextOut) ∧
      (isAllocVar next → isStackVar nextOut) ∧ ssaMapOK nextOut ssaOut := by
  have shifted : isAllocVar (next + 2) ∨ isStackVar (next + 2) :=
    h.1.elim (fun stacked => Or.inl (isStackVarFlip next stacked))
      (fun allocated => Or.inr (isAllocVarFlip next allocated))
  obtain ⟨bound, allocated, stacked, mapOK⟩ :=
    listNextVarRenameProps names ssa (next + 2) namesOut ssaOut nextOut produced ⟨shifted, h.2⟩
  exact ⟨bound, fun input => allocated (isStackVarFlip next input),
    fun input => stacked (isAllocVarFlip next input), mapOK⟩

/-- Full original shifted move-list wrapper. Its original map bound is at the
unshifted counter; the shifted bound is derived, and allocation/stack classes
swap exactly as in the source. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_move_props_2"
  (words_as_type_indexed_bitvec)]
theorem listNextVarRenameMoveProps2 {width : Nat} [NeZero width]
    (names : List Nat) (ssa : Spt Nat) (next : Nat)
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : listNextVarRenameMove ssa (next + 2) names = (output, ssaOut, nextOut))
    (h : (isAllocVar next ∨ isStackVar next) ∧ ssaMapOK next ssa) :
    next + 2 ≤ nextOut ∧ (isAllocVar next → isStackVar nextOut) ∧
      (isStackVar next → isAllocVar nextOut) ∧ ssaMapOK nextOut ssaOut := by
  have shifted : isAllocVar (next + 2) ∨ isStackVar (next + 2) :=
    h.1.elim (fun allocated => Or.inr (isAllocVarFlip next allocated))
      (fun stacked => Or.inl (isStackVarFlip next stacked))
  obtain ⟨bound, allocated, stacked, mapOK⟩ :=
    listNextVarRenameMoveProps names ssa (next + 2) output ssaOut nextOut produced
      ⟨shifted, ssaMapOKLem next ssa h.2⟩
  exact ⟨bound, fun input => stacked (isAllocVarFlip next input),
    fun input => allocated (isStackVarFlip next input), mapOK⟩

end Flapjack.Compiler.Backend.WordAlloc
