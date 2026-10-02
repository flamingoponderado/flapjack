import Flapjack.Compiler.Backend.LabToTarget.SectionLookupPositions
import Flapjack.Compiler.Backend.LabToTarget.ComputedLabelPreservation
import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity
import Flapjack.Compiler.Backend.LabToTarget.ValidityNop

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabProps.LabelSets Flapjack.Basis.Pure.MlString

/-- Full original whole-code lookup result, with all six source guards and an
arbitrary actual nested-map accumulator. The source's final `nop : β` binder is
retained at its independent generic carrier, even though it occurs in neither
guards nor conclusion. No word-byte specialization is made. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "lab_lookup_compute_labels_test" (words_as_type_indexed_bitvec)]
theorem labLookup_computeLabels_position {width : Nat} [NeZero width]
    (pos : Nat) (code : List (Section
      (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (acc : Spt (Spt Nat)) (sectionId labelId pc : Nat) (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) {β : Type u} (_nop : β) :
    (∀ sec ∈ code, secLabelsOk sec) ∧
    (code.map (fun sec => sec.sectionId)).Nodup ∧
    (∀ sec ∈ code, (extractLabels sec.lines).Nodup) ∧
    (∀ sec ∈ code, secLabelZero sec) ∧
    allEncOk c labs ffis pos code ∧ locToPc sectionId labelId code = some pc →
    labLookup sectionId labelId (computeLabelsAlt pos code acc) = some (posVal pc pos code) := by
  clear _nop
  induction code generalizing pos acc pc with
  | nil => rintro ⟨_,_,_,_,_,hpc⟩; simp [locToPc] at hpc
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    rintro ⟨hvalid,hids,hlabels,hzero,henc,hpc⟩
    have hvalidTail : ∀ sec ∈ rest, secLabelsOk sec := fun sec hm => hvalid sec (by simp [hm])
    have hlabelsTail : ∀ sec ∈ rest, (extractLabels sec.lines).Nodup := fun sec hm => hlabels sec (by simp [hm])
    have hzeroTail : ∀ sec ∈ rest, secLabelZero sec := fun sec hm => hzero sec (by simp [hm])
    have hvalidLines : ∀ line ∈ lines, secLabelOk sid line := hvalid ⟨sid,lines⟩ (by simp)
    have hlabelLines := hlabels ⟨sid,lines⟩ (by simp)
    have hzeroLines : ∀ line ∈ lines, labelZero line := hzero ⟨sid,lines⟩ (by simp)
    simp only [List.map_cons,List.nodup_cons] at hids
    have hencParts := (allEncOk_cons c labs ffis lines pos sid rest).mp henc
    have hlength := linesEncWithNop_lengthOk c.encode labs ffis pos lines
      (linesOk_linesEncWithNop c labs ffis pos lines hencParts.2.2)
    generalize hentry : sectionLabels pos lines [] = entry
    rcases entry with ⟨newPos,secLabs⟩
    have hnew : newPos = pos + (lines.map lineLength).sum := by
      have hh := sectionLabelsSecLength pos lines []
      rw [hentry] at hh
      rw [secLength_sumLineLength lines pos hlength] at hh
      simpa [Nat.add_comm] using hh
    subst newPos
    have tailCase (j : Nat) (heq : pc = lenNoLab lines + j)
        (htpc : locToPc sectionId labelId rest = some j) :
        labLookup sectionId labelId
          (computeLabelsAlt pos (⟨sid,lines⟩::rest) acc) =
            some (posVal pc pos (⟨sid,lines⟩::rest)) := by
      subst pc
      have hnone := secPosVal_tooBig (lenNoLab lines + j) pos lines (by omega)
      have ht := ih (pos + (lines.map lineLength).sum)
        (sptInsert sid (sptFromAList ((0,pos)::secLabs)) acc) j
        ⟨hvalidTail,hids.2,hlabelsTail,hzeroTail,hencParts.1,htpc⟩
      rw [computeLabelsAlt, hentry, posVal_decompose]
      dsimp only
      rw [hnone]
      simpa only [Nat.add_sub_cancel_left] using ht
    rw [locToPc_sections sectionId labelId (⟨sid,lines⟩::rest) hvalid] at hpc
    by_cases hsid : sectionId = sid
    · subst sectionId
      cases hloc : secLocToPc labelId lines with
      | none =>
        cases hrest : locToPc sid labelId rest with
        | none => simp [hloc,hrest] at hpc
        | some j =>
          apply tailCase j
          · simpa [hloc,hrest] using hpc.symm
          · exact hrest
      | some j =>
        have heq : j = pc := by simpa [hloc] using hpc
        subst pc
        have hlookup : labLookup sid labelId
            (computeLabelsAlt pos (⟨sid,lines⟩::rest) acc) =
              sptAListLookup labelId ((0,pos)::secLabs) := by
          simp only [computeLabelsAlt,hentry]
          rw [labLookup_computeLabelsAlt_ignore _ rest _ sid labelId hids.1]
          simp [labLookup,sptLookup_sptInsert_same,sptLookup_sptFromAList]
        rw [hlookup]
        by_cases hkey : labelId = 0
        · subst labelId
          have hz : secLocToPc (width := width) 0 lines = some 0 := by
            rw [secLocToPc.eq_def]
            simp
          have hj : j = 0 := Option.some.inj (hloc.symm.trans hz)
          subst j
          rw [posVal_zero (⟨sid,lines⟩::rest) c labs ffis pos henc]
          simp [sptAListLookup]
        · have hsection := sectionLabels_lookup_position pos lines [] j sid labelId
            ⟨hvalidLines,hlength,hzeroLines,hlabelLines,hloc,hkey⟩
          rcases hsection with ⟨i,hi,hboundary|hvalue⟩
          · have hindex : j = lenNoLab lines := by simpa [lenNoLab] using hboundary.2.2
            have hi' : sptAListLookup labelId secLabs = some i := by simpa [hentry] using hi
            rw [posVal_decompose]
            dsimp only
            rw [hboundary.1,hindex,Nat.sub_self,
              posVal_zero rest c labs ffis _ hencParts.1]
            simpa [sptAListLookup,hkey,hboundary.2.1] using hi'
          · have hi' : sptAListLookup labelId secLabs = some i := by simpa [hentry] using hi
            rw [posVal_decompose]
            dsimp only
            rw [hvalue]
            simpa [sptAListLookup,hkey] using hi'
    · cases hrest : locToPc sectionId labelId rest with
      | none => simp [hsid,hrest] at hpc
      | some j =>
        apply tailCase j
        · simpa [hsid,hrest] using hpc.symm
        · exact hrest

end Flapjack.Compiler.Backend.LabToTarget
