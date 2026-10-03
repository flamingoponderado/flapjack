import Flapjack.Compiler.Backend.LabToTarget.SectionLabelExtraction
import Flapjack.Compiler.Backend.LabToTarget.LabsDomain
import Flapjack.Misc.Sptree.ToAList
import Mathlib.Data.Set.Lattice
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps.LabelSets

/-- Local image/domain calculation for the original section-label accumulator.
This is Flapjack proof infrastructure, not an independently named HOL theorem. -/
private theorem sectionLabels_fromAList_domain {width : Nat} [NeZero width]
    (pos : Nat) (sec : Section (LabLineHOL width)) (newPos : Nat) (secLabs : List (Nat × Nat))
    (heq : sectionLabels pos sec.lines [] = (newPos,secLabs)) :
    (fun n => (sec.sectionId,n)) '' sptDomain (sptFromAList ((0,pos)::secLabs)) = secGetCodeLabels sec := by
  have hkeys := sectionLabels_codeLabels pos sec.lines [] newPos secLabs heq
  have hd : (sptDomain (sptFromAList ((0,pos)::secLabs)) : Set Nat) =
      insert 0 {n | ∃ l ∈ sec.lines,n ∈ lineGetCodeLabels l} := by
    rw [sptDomainFromAList]
    ext n
    change n ∈ ((0,pos)::secLabs).map Prod.fst ↔
      n ∈ (insert 0 {n | ∃ l ∈ sec.lines,n ∈ lineGetCodeLabels l} : Set Nat)
    simp only [List.map_cons, List.mem_cons, Set.mem_insert_iff, Set.mem_ofPred_eq]
    have hn := congrArg (fun s : Set Nat => n ∈ s) hkeys
    simpa [Set.mem_insert_iff,Set.mem_union] using hn
  rw [hd]
  ext p
  change (∃ n,(n = 0 ∨ ∃ l ∈ sec.lines,n ∈ lineGetCodeLabels l) ∧ (sec.sectionId,n) = p) ↔
    p = (sec.sectionId,0) ∨ ∃ n,(∃ l ∈ sec.lines,n ∈ lineGetCodeLabels l) ∧ p = (sec.sectionId,n)
  constructor
  · rintro ⟨n,hn,hp⟩
    rcases hn with h0 | hn
    · subst n
      exact Or.inl hp.symm
    · exact Or.inr ⟨n,hn,hp.symm⟩
  · rintro (h0 | ⟨n,hn,hp⟩)
    · exact ⟨0,Or.inl rfl,h0.symm⟩
    · exact ⟨n,Or.inr hn,hp.symm⟩

/-- Full original computed label-domain theorem. Both original guards are
retained: distinct section numbers and disjointness from the initial outer map. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "labs_domain_compute_labels_alt" (words_as_type_indexed_bitvec)]
theorem labsDomain_computeLabelsAlt {width : Nat} [NeZero width] (pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (labs : Spt (Spt Nat)) :
    (code.map (fun sec => sec.sectionId)).Nodup ∧
    Disjoint (sptDomain labs) {n | n ∈ code.map (fun sec => sec.sectionId)} →
      labsDomain (computeLabelsAlt pos code labs) = getCodeLabels code ∪ labsDomain labs := by
  induction code generalizing pos labs with
  | nil => simp [computeLabelsAlt,getCodeLabels]
  | cons sec rest ih =>
    rintro ⟨hnd,hd⟩
    have htail : sec.sectionId ∉ rest.map (fun sec => sec.sectionId) ∧
        (rest.map (fun sec => sec.sectionId)).Nodup := by simpa using hnd
    have hfresh : ¬sptDomain labs sec.sectionId := by
      intro hm
      exact Set.disjoint_left.mp hd hm (by simp)
    generalize hsec : sectionLabels pos sec.lines [] = entry
    rcases entry with ⟨newPos,secLabs⟩
    let inner := sptFromAList ((0,pos)::secLabs)
    have hdisj : Disjoint (sptDomain (sptInsert sec.sectionId inner labs))
        {n | n ∈ rest.map (fun sec => sec.sectionId)} := by
      apply Set.disjoint_left.mpr
      intro n hn hm
      change n ∈ rest.map (fun sec => sec.sectionId) at hm
      rw [sptDomainInsert] at hn
      rcases hn with rfl | hn
      · exact htail.1 hm
      · exact Set.disjoint_left.mp hd hn (List.mem_cons_of_mem sec.sectionId hm)
    simp only [computeLabelsAlt,hsec]
    change labsDomain (computeLabelsAlt newPos rest (sptInsert sec.sectionId inner labs)) = _
    rw [ih newPos (sptInsert sec.sectionId inner labs) ⟨htail.2,hdisj⟩]
    rw [labsDomain_insert sec.sectionId inner labs hfresh]
    rw [sectionLabels_fromAList_domain pos sec newPos secLabs hsec]
    rw [getCodeLabels_cons]
    simp only [Set.union_left_comm,Set.union_comm]
end Flapjack.Compiler.Backend.LabToTarget
