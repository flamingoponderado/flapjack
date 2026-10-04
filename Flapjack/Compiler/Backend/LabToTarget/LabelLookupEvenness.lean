import Flapjack.Compiler.Backend.LabToTarget.ValidityNop
import Flapjack.Compiler.Backend.LabToTarget.SectionLength
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack infrastructure: full validity equates recorded and physical length.
No independently named original theorem is claimed for this projection. -/
private theorem lineOk_annotationLength {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (line : LabLineHOL width) (h : lineOk c labs ffis pos line) :
    lineLen line = lineLength line := by
  have hl := lineEncWithNop_lengthOk c.encode labs ffis pos line
    (lineOk_lineEncWithNop c labs ffis pos line h)
  cases line with
  | label sid lid len =>
    have hz : len = 0 := by simpa [lineLengthOk,lineBytes,lineLen] using hl.symm
    simp [lineLen,lineLength,hz]
  | asm _ _ _ => simpa [lineLengthOk,lineBytes,lineLen,lineLength] using hl.symm
  | labAsm _ _ _ _ => simpa [lineLengthOk,lineBytes,lineLen,lineLength] using hl.symm

/-- Full original association-list lookup theorem, with all three source guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem linesOk_sectionLabels_lookup_even {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (acc : List (Nat × Nat)) (key value : Nat) :
    linesOk c labs ffis pos lines ∧
    (∀ k x,sptAListLookup k acc = some x → x % 2 = 0) ∧
    sptAListLookup key (sectionLabels pos lines acc).2 = some value → value % 2 = 0 := by
  induction lines generalizing pos acc with
  | nil => rintro ⟨_,ha,hl⟩; exact ha key value hl
  | cons line rest ih =>
    rintro ⟨hp,ha,hl⟩
    have hlength := lineOk_annotationLength c labs ffis pos line hp.1
    have ht : linesOk c labs ffis (pos + lineLen line) rest := by simpa [hlength] using hp.2
    cases line with
    | label sid lid len =>
      have hh : pos % 2 = 0 ∧ len = 0 := hp.1
      rcases hh with ⟨he,rfl⟩
      simp only [lineLen,Nat.add_zero] at ht
      by_cases hid : lid = 0
      · simp only [sectionLabels,if_pos hid,Nat.add_zero] at hl
        exact ih pos acc ⟨ht,ha,hl⟩
      · simp only [sectionLabels,if_neg hid,Nat.add_zero] at hl
        apply ih pos ((lid,pos)::acc) ⟨ht,?_,hl⟩
        intro k x hx
        by_cases hk : k = lid
        · simp [sptAListLookup,hk] at hx
          subst x
          exact he
        · exact ha k x (by simpa [sptAListLookup,hk] using hx)
    | asm instruction bytes len =>
      simp only [lineLen] at ht
      simp only [sectionLabels] at hl
      exact ih (pos + len) acc ⟨ht,ha,hl⟩
    | labAsm instruction word bytes len =>
      simp only [lineLen] at ht
      simp only [sectionLabels] at hl
      exact ih (pos + len) acc ⟨ht,ha,hl⟩

/-- Full original split at the actual annotated section length. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncOk_split {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos k : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (rest : List (Section (LabLineHOL width))) :
    allEncOk c labs ffis pos (⟨k,lines⟩::rest) →
      allEncOk c labs ffis pos [⟨k,lines⟩] ∧
      allEncOk c labs ffis (pos + secLength lines 0) rest := by
  rw [allEncOk_cons]
  rintro ⟨ht,he,hl⟩
  have hlength := secLength_sumLineLength lines 0
    (linesEncWithNop_lengthOk c.encode labs ffis pos lines
      (linesOk_linesEncWithNop c labs ffis pos lines hl))
  constructor
  · rw [allEncOk_cons]
    exact ⟨by simp [allEncOk],he,hl⟩
  · simpa [hlength] using ht

/-- Full original section-end evenness under actual encoding validity. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncOk_even {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (k : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) :
    allEncOk c labs ffis pos [⟨k,lines⟩] → (secLength lines pos) % 2 = 0 := by
  rw [allEncOk_cons]
  rintro ⟨_,he,hl⟩
  have hlength := secLength_sumLineLength lines pos
    (linesEncWithNop_lengthOk c.encode labs ffis pos lines
      (linesOk_linesEncWithNop c labs ffis pos lines hl))
  simpa [hlength,Nat.add_comm] using he
/-- Full original computed lookup evenness: validity, the actual returned lookup,
old same-key lookup parity, and initial evenness are the four source guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncOk_computeLabels_lookup_even {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (outer inner : Nat) (acc : Spt (Spt Nat)) (value : Nat) :
    allEncOk c labs ffis pos code ∧
    labLookup outer inner (computeLabelsAlt pos code acc) = some value ∧
    (∀ x,labLookup outer inner acc = some x → x % 2 = 0) ∧ pos % 2 = 0 → value % 2 = 0 := by
  induction code generalizing pos acc with
  | nil => rintro ⟨_,hl,ha,_⟩; exact ha value hl
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    rintro ⟨hv,hl,ha,he⟩
    have hs := allEncOk_split c labs ffis pos k lines rest hv
    have hend := allEncOk_even c labs ffis k lines pos hs.1
    have hlines := (allEncOk_cons c labs ffis lines pos k []).mp hs.1
    generalize hsec : sectionLabels pos lines [] = entry
    rcases entry with ⟨newPos,secLabs⟩
    have hp : newPos = secLength lines pos := by
      have hn := sectionLabelsSecLength pos lines []
      simpa [hsec] using hn
    have ht : allEncOk c labs ffis newPos rest := by
      have hadd : secLength lines pos = secLength lines 0 + pos := by
        simpa using secLengthAdd lines 0 pos
      have hpos : newPos = pos + secLength lines 0 := by omega
      simpa [hpos] using hs.2
    let tree := sptFromAList ((0,pos)::secLabs)
    have hacc : ∀ x,labLookup outer inner (sptInsert k tree acc) = some x → x % 2 = 0 := by
      intro x hx
      by_cases hk : outer = k
      · subst outer
        simp only [labLookup,sptLookup_sptInsert_same] at hx
        change sptLookup inner (sptFromAList ((0,pos)::secLabs)) = some x at hx
        rw [sptLookup_sptFromAList] at hx
        by_cases hzero : inner = 0
        · simp [sptAListLookup,hzero] at hx
          subst x
          exact he
        · have hlookup : sptAListLookup inner secLabs = some x := by
            simpa [sptAListLookup,hzero] using hx
          apply linesOk_sectionLabels_lookup_even c labs ffis pos lines [] inner x
          refine ⟨hlines.2.2,?_,?_⟩
          · intro key value hvalue
            simp [sptAListLookup] at hvalue
          · simpa [hsec] using hlookup
      · apply ha x
        simpa only [labLookup,sptLookup_sptInsert_ne k outer tree acc hk] using hx
    simp only [computeLabelsAlt,hsec] at hl
    exact ih newPos (sptInsert k tree acc) ⟨ht,hl,hacc,by simpa [hp] using hend⟩
end Flapjack.Compiler.Backend.LabToTarget
