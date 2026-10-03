import Flapjack.Compiler.Backend.LabToTarget.ShmemNames
import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity
import Flapjack.Compiler.Encoders.AsmProps.Encoding
import Flapjack.Compiler.Backend.Semantics.TargetSem.MmioIndex
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩

/-- Flapjack infrastructure eliminating every EL from the original MMIO
boundary using its own source bounds. The result contains only checked list
accesses, so no empty-head or past-end arbitrary value enters this predicate.
There is no separately named HOL declaration for this syntax conversion. -/
theorem mmioBoundary_boundedLookup (names : List HolFfiName) (index : Nat) :
    mmioIndexBoundary names index ↔
    index ≤ names.length ∧
      (∀ j, j < index → ∃ hj : j < names.length,
        ∃ name, names[j]'hj = .extCall name) ∧
      (∀ j, index ≤ j → ∀ hj : j < names.length,
        ∃ op, names[j]'hj = .sharedMem op) := by
  constructor
  · rintro ⟨hb,hpre,hsuf⟩
    refine ⟨hb,?_,?_⟩
    · intro j hj
      have hbound : j < names.length := by omega
      obtain ⟨name,he⟩ := hpre j hj
      exact ⟨hbound,name,(holEl_eq_getElem j names hbound).symm.trans he⟩
    · intro j hj hbound
      obtain ⟨op,he⟩ := hsuf j hj hbound
      exact ⟨op,(holEl_eq_getElem j names hbound).symm.trans he⟩
  · rintro ⟨hb,hpre,hsuf⟩
    refine ⟨hb,?_,?_⟩
    · intro j hj
      obtain ⟨hbound,name,he⟩ := hpre j hj
      exact ⟨name,(holEl_eq_getElem j names hbound).trans he⟩
    · intro j hj hbound
      obtain ⟨op,he⟩ := hsuf j hj hbound
      exact ⟨op,(holEl_eq_getElem j names hbound).trans he⟩

/-- Full original MMIO append law. Every EL in the existing boundary is
eliminated under its original bounds; the existing optional-choice definition
and all arbitrary defaults remain untouched. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "mmio_pcs_min_index_APPEND_thm"]
theorem mmioPcsMinIndex_append (l ffis : List HolFfiName) :
    (∀ x ∈ l, ∀ s, x ≠ HolFfiName.extCall s) ∧
    (∀ x ∈ ffis, ∃ s, x = HolFfiName.extCall s) →
    mmioPcsMinIndex (ffis++l) = some ffis.length := by
  rintro ⟨hl,hffis⟩
  apply mmioPcsMinIndex_eq_some
  rw [mmioBoundary_boundedLookup]
  refine ⟨by simp,?_,?_⟩
  · intro j hj
    have hb : j < (ffis++l).length := by simp; omega
    obtain ⟨name,he⟩ := hffis ffis[j] (List.getElem_mem hj)
    exact ⟨hb,name,by simpa only [List.getElem_append_left hj] using he⟩
  · intro j hj hb
    have hs : j-ffis.length < l.length := by simp at hb; omega
    cases hx : l[j-ffis.length]'hs with
    | extCall name => exact False.elim (hl _ (List.getElem_mem hs) name hx)
    | sharedMem op =>
      exact ⟨op,by rw [List.getElem_append_right hj]; exact hx⟩

/-- Full original extraction-index law. Original encoding guards are retained
although the name-classification proof already suffices; no extra bounds or
assumed desired MMIO index are added. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "mmio_pcs_min_index_get_shmem_info_ok" (words_as_type_indexed_bitvec)]
theorem mmioPcsMinIndex_getShmemInfo {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (validFfis : List HolFfiName)
    (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (ffis : List HolFfiName) (p : Nat) (newFfiNames : List HolFfiName)
    (newShmemInfo : List ShmemInfoNum) :
    allEncOk c labs validFfis validPos code ∧ encOk c ∧
    (∀ x ∈ ffis, ∃ s, x = HolFfiName.extCall s) ∧
    getShmemInfo code p ffis [] = (newFfiNames,newShmemInfo) →
    mmioPcsMinIndex newFfiNames = some ffis.length := by
  rintro ⟨_he,_hc,hffis,hout⟩
  obtain ⟨l,hnames,hl⟩ := getShmemInfo_mappedNames code p ffis [] newFfiNames newShmemInfo hout
  rw [hnames]
  apply mmioPcsMinIndex_append
  refine ⟨?_,hffis⟩
  intro x hx s
  obtain ⟨op,rfl⟩ := hl x hx
  intro h
  cases h
end Flapjack.Compiler.Backend.LabToTarget
