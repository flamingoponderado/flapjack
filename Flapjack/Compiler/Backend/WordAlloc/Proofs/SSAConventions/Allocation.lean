import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameLookup
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.ListNextVarRenameArithmetic

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack factoring of the original renaming arithmetic and lookup proof
steps. No separately named HOL theorem exists for this helper. The actual
producer equation proves stack class for the whole translated cutset. -/
theorem ssaRenamedStackNames {width : Nat} [NeZero width]
    (ssa : Spt Nat) (next : Nat) (cutsets : WordLangCutsetsHOL)
    (move : WordLangProgHOL (BitVec width)) (mapOut : Spt Nat) (nextOut : Nat)
    (produced : listNextVarRenameMove ssa (next + 2)
      ((sptToAList (sptUnion cutsets.1 cutsets.2)).map Prod.fst) = (move, mapOut, nextOut))
    (allocated : isAllocVar next) :
    everyNameHOL isStackVar (applyNummapsKey (optionLookup mapOut) cutsets) = true := by
  let keys := (sptToAList (sptUnion cutsets.1 cutsets.2)).map Prod.fst
  change listNextVarRenameMove ssa (next + 2) keys = (move, mapOut, nextOut) at produced
  unfold listNextVarRenameMove at produced
  generalize raw : listNextVarRename keys ssa (next + 2) = result at produced
  rcases result with ⟨registers, renamed, counter⟩
  simp only [Prod.mk.injEq] at produced
  rcases produced with ⟨_, rfl, rfl⟩
  have arithmetic := listNextVarRenameLemma1 keys ssa (next + 2) registers renamed counter raw
  have lookup := listNextVarRenameLemma2Prime keys ssa (next + 2) registers renamed counter
    raw (sptAllDistinctMapFstToAList (sptUnion cutsets.1 cutsets.2))
  rw [everyName_def2]
  apply List.all_eq_true.mpr
  intro key member
  have domain := (sptMemMapFstToAList _ key).mp member
  rw [union_applyNummapsKey, applyNummapKeyDomain] at domain
  rcases domain with ⟨source, sourceDomain, equal⟩
  have sourceMember : source ∈ keys :=
    (sptMemMapFstToAList (sptUnion cutsets.1 cutsets.2) source).mpr sourceDomain
  have registerMember : optionLookup renamed source ∈ registers := by
    rw [lookup.1]
    apply List.mem_map.mpr
    refine ⟨source, sourceMember, ?_⟩
    cases read : sptLookup source renamed <;> simp [optionLookup, read]
  rw [arithmetic.2.1] at registerMember
  obtain ⟨index, _, generated⟩ := List.mem_map.mp registerMember
  rw [← equal, ← generated]
  simp only [isAllocVar, isStackVar, decide_eq_true_eq] at allocated ⊢
  omega

/-- Flapjack Boolean factoring: the actual rename-move producer emits only
a Move, independently of its source map. No separate HOL original exists. -/
theorem ssaRenameMove_preAlloc {width : Nat} [NeZero width]
    (ssa : Spt Nat) (next : Nat) (keys : List Nat) :
    preAllocConventionsHOL (listNextVarRenameMove (width := width) ssa next keys).1 = true := by
  simp [listNextVarRenameMove, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original Alloc case: actual stack names are proved from the source
producer, without assuming target conventions. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocAlloc {width : Nat} [NeZero width]
    (destination : Nat) (cutsets : WordLangCutsetsHOL)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL
      (ssaCcTrans (.alloc destination cutsets : WordLangProgHOL (BitVec width)) ssa next tables).1 = true := by
  generalize produced : listNextVarRenameMove (width := width) ssa (next + 2)
    ((sptToAList (sptUnion cutsets.1 cutsets.2)).map Prod.fst) = result
  rcases result with ⟨move, renamed, counter⟩
  have stack := ssaRenamedStackNames ssa next cutsets move renamed counter produced h.1
  have movePre := ssaRenameMove_preAlloc (width := width) ssa (next + 2)
    ((sptToAList (sptUnion cutsets.1 cutsets.2)).map Prod.fst)
  rw [produced] at movePre
  simp only [ssaCcTrans, produced, preAllocConventionsHOL,
    everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at movePre ⊢
  simp [stack, movePre, listNextVarRenameMove, everyStackVarHOL, callArgConventionHOL]

/-- Original Install case with actual whole-cutset stack class derived. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocInstall {width : Nat} [NeZero width]
    (ptr len dptr dlen : Nat) (cutsets : WordLangCutsetsHOL)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL
      (ssaCcTrans (.install ptr len dptr dlen cutsets : WordLangProgHOL (BitVec width))
        ssa next tables).1 = true := by
  generalize produced : listNextVarRenameMove (width := width) ssa (next + 2)
    ((sptToAList (sptUnion cutsets.1 cutsets.2)).map Prod.fst) = result
  rcases result with ⟨move, renamed, counter⟩
  have stack := ssaRenamedStackNames ssa next cutsets move renamed counter produced h.1
  have movePre := ssaRenameMove_preAlloc (width := width) ssa (next + 2)
    ((sptToAList (sptUnion cutsets.1 cutsets.2)).map Prod.fst)
  rw [produced] at movePre
  simp only [ssaCcTrans, produced, preAllocConventionsHOL,
    everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at movePre ⊢
  simp [stack, movePre, nextVarRename, listNextVarRenameMove,
    everyStackVarHOL, callArgConventionHOL]

/-- Original FFI case retains the full arbitrary input operands and cutsets. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocFFI {width : Nat} [NeZero width]
    (index : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 : Nat) (cutsets : WordLangCutsetsHOL)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL
      (ssaCcTrans (.ffi index ptr len ptr2 len2 cutsets : WordLangProgHOL (BitVec width))
        ssa next tables).1 = true := by
  generalize produced : listNextVarRenameMove (width := width) ssa (next + 2)
    ((sptToAList (sptUnion cutsets.1 cutsets.2)).map Prod.fst) = result
  rcases result with ⟨move, renamed, counter⟩
  have stack := ssaRenamedStackNames ssa next cutsets move renamed counter produced h.1
  have movePre := ssaRenameMove_preAlloc (width := width) ssa (next + 2)
    ((sptToAList (sptUnion cutsets.1 cutsets.2)).map Prod.fst)
  rw [produced] at movePre
  simp only [ssaCcTrans, produced, preAllocConventionsHOL,
    everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at movePre ⊢
  simp [stack, movePre, listNextVarRenameMove, everyStackVarHOL, callArgConventionHOL]

end Flapjack.WordAlloc
