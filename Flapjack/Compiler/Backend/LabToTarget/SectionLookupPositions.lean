import Flapjack.Compiler.Backend.LabToTarget.SectionLookupPreservation
import Flapjack.Compiler.Backend.LabProps.LabelExtractionValidity
import Flapjack.Compiler.Backend.LabToTarget.PositionValues.ZeroLabels
import Flapjack.Compiler.Backend.LabToTarget.SectionNavigation
import Flapjack.Compiler.Backend.LabToTarget.LengthCorrectness

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabProps.LabelSets Flapjack.Basis.Pure.MlString

/-- Flapjack induction infrastructure: zero-length label-only tails have zero
physical length. No independently named HOL declaration is claimed. -/
private theorem labelOnly_zeroLength {width : Nat} [NeZero width]
    (lines : List (LabLineHOL width))
    (hc : ∀ line ∈ lines, isLabelHOL line = true)
    (hz : ∀ line ∈ lines, labelZero line) : (lines.map lineLength).sum = 0 := by
  induction lines with
  | nil => rfl
  | cons line rest ih =>
    have hcHead := hc line (by simp)
    have hzHead := hz line (by simp)
    have ht := ih (fun l h => hc l (by simp [h])) (fun l h => hz l (by simp [h]))
    cases line <;> simp_all [isLabelHOL,labelZero,lineLength]

/-- Full original section lookup theorem. All six guards are retained, and the
existential includes both the exhausted boundary and successful position cases. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem sectionLabels_lookup_position {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (acc : List (Nat × Nat)) (pc owner key : Nat) :
    (∀ line ∈ lines, secLabelOk owner line) ∧
    (∀ line ∈ lines, lineLengthOk line) ∧
    (∀ line ∈ lines, labelZero line) ∧
    (extractLabels lines).Nodup ∧ secLocToPc key lines = some pc ∧ key ≠ 0 →
    ∃ i, sptAListLookup key (sectionLabels pos lines acc).2 = some i ∧
      ((secPosVal pc pos lines = none ∧ i = pos + (lines.map lineLength).sum ∧
        pc = (lines.filter (fun line => !isLabelHOL line)).length) ∨
       secPosVal pc pos lines = some i) := by
  induction lines generalizing pos acc pc with
  | nil =>
    rintro ⟨_,_,_,_,hpc,hkey⟩
    simp [secLocToPc,hkey] at hpc
  | cons line rest ih =>
    rintro ⟨hsec,hlen,hzero,hnd,hpc,hkey⟩
    have hs : ∀ l ∈ rest, secLabelOk owner l := fun l h => hsec l (by simp [h])
    have hl : ∀ l ∈ rest, lineLengthOk l := fun l h => hlen l (by simp [h])
    have hz : ∀ l ∈ rest, labelZero l := fun l h => hzero l (by simp [h])
    cases line with
    | label sid lid len =>
      have hhead : sid = owner ∧ lid ≠ 0 := hsec (.label sid lid len) (by simp)
      have hlen0 : len = 0 := hzero (.label sid lid len) (by simp)
      subst len
      simp only [extractLabels,List.nodup_cons] at hnd
      by_cases hid : lid = key
      · subst lid
        have hpc0 : pc = 0 := by simpa [secLocToPc,hkey] using hpc.symm
        subst pc
        have hnot : key ∉ (extractLabels rest).map Prod.snd := by
          intro hm
          rcases List.mem_map.mp hm with ⟨⟨a,b⟩,hm,he⟩
          have hh := secLabelOk_extractLabels owner rest a b ⟨hs,hm⟩
          have ha : a = sid := hh.1.trans hhead.1.symm
          have hb : b = key := he
          subst a
          subst b
          exact hnd.1 hm
        have hlookup := sectionLabels_lookup_ignore pos rest ((key,pos)::acc) key hnot
        refine ⟨pos,?_,?_⟩
        · simpa [sectionLabels,hkey,sptAListLookup] using hlookup
        · by_cases hc : ∀ l ∈ rest, isLabelHOL l = true
          · left
            have hnone := everyIsLabel_secPosVal 0 pos rest hc
            have hsum := labelOnly_zeroLength rest hc hz
            have hfilter : rest.filter (fun l => !isLabelHOL l) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro l hm
              simp [hc l hm]
            refine ⟨?_,?_,?_⟩
            · simpa [secPosVal,isLabelHOL,lineLength] using hnone
            · simp [lineLength,hsum]
            · change 0 = (rest.filter (fun l => !isLabelHOL l)).length
              rw [hfilter]
              rfl
          · right
            simpa [secPosVal,isLabelHOL,lineLength] using secPosVal_zero pos rest ⟨hc,hz⟩
      · have htpc : secLocToPc key rest = some pc := by
          simpa [secLocToPc,hkey,hid,isLabelHOL] using hpc
        have ht := ih pos ((lid,pos)::acc) pc ⟨hs,hl,hz,hnd.2,htpc,hkey⟩
        simpa [sectionLabels,hhead.2,secPosVal,isLabelHOL,lineLength] using ht
    | asm instruction bytes len =>
      have hlength : len = bytes.length := by
        simpa [lineLengthOk,lineBytes,lineLen] using (hlen (.asm instruction bytes len) (by simp)).symm
      subst len
      simp only [extractLabels] at hnd
      cases hrest : secLocToPc key rest with
      | none => simp [secLocToPc,hkey,isLabelHOL,hrest] at hpc
      | some n =>
        have heq : n + 1 = pc := by simpa [secLocToPc,hkey,isLabelHOL,hrest] using hpc
        subst pc
        rcases ih (pos + bytes.length) acc n ⟨hs,hl,hz,hnd,hrest,hkey⟩ with ⟨i,hlookup,hresult⟩
        refine ⟨i,by simpa [sectionLabels] using hlookup,?_⟩
        rcases hresult with hb | hv
        · left
          simpa [secPosVal,isLabelHOL,lineLength,Nat.add_assoc] using hb
        · right
          simpa [secPosVal,isLabelHOL,lineLength] using hv
    | labAsm instruction word bytes len =>
      have hlength : len = bytes.length := by
        simpa [lineLengthOk,lineBytes,lineLen] using (hlen (.labAsm instruction word bytes len) (by simp)).symm
      subst len
      simp only [extractLabels] at hnd
      cases hrest : secLocToPc key rest with
      | none => simp [secLocToPc,hkey,isLabelHOL,hrest] at hpc
      | some n =>
        have heq : n + 1 = pc := by simpa [secLocToPc,hkey,isLabelHOL,hrest] using hpc
        subst pc
        rcases ih (pos + bytes.length) acc n ⟨hs,hl,hz,hnd,hrest,hkey⟩ with ⟨i,hlookup,hresult⟩
        refine ⟨i,by simpa [sectionLabels] using hlookup,?_⟩
        rcases hresult with hb | hv
        · left
          simpa [secPosVal,isLabelHOL,lineLength,Nat.add_assoc] using hb
        · right
          simpa [secPosVal,isLabelHOL,lineLength] using hv

end Flapjack.Compiler.Backend.LabToTarget
