import Flapjack.Compiler.Backend.LabToTarget.ProgramByteLengths
import Flapjack.Compiler.Backend.LabToTarget.Fetch
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original unrestricted accumulator equation, retaining its position
split guard and arbitrary label annotations without an encoding premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_acc_sum" (words_as_type_indexed_bitvec)]
theorem posVal_accSum {width : Nat} [NeZero width]
    (i pos : Nat) (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (x y : Nat) :
    x + y = pos → x + posVal i y secs = posVal i pos secs := by
  rintro rfl
  induction secs generalizing i y with
  | nil => simp [posVal]
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    induction lines generalizing i y with
    | nil => simpa only [posVal] using ih i y
    | cons line lines ihLines =>
      cases line with
      | label a b len =>
        simpa only [posVal,isLabelHOL,↓reduceIte,lineLength,Nat.add_assoc]
          using ihLines i (y + (if len = 0 then 0 else 1))
      | asm a bytes len =>
        cases i with
        | zero => simp [posVal,isLabelHOL]
        | succ i =>
          simpa only [posVal,isLabelHOL,Bool.false_eq_true,↓reduceIte,
            Nat.succ_ne_zero,Nat.add_one_sub_one,lineLength,Nat.add_assoc]
            using ihLines i (y + bytes.length)
      | labAsm a w bytes len =>
        cases i with
        | zero => simp [posVal,isLabelHOL]
        | succ i =>
          simpa only [posVal,isLabelHOL,Bool.false_eq_true,↓reduceIte,
            Nat.succ_ne_zero,Nat.add_one_sub_one,lineLength,Nat.add_assoc]
            using ihLines i (y + bytes.length)

/-- Full original zero-base accumulator transport with no validity guard. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_acc_0" (words_as_type_indexed_bitvec)]
theorem posVal_accZero {width : Nat} [NeZero width]
    (i pos : Nat) (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    pos + posVal i 0 secs = posVal i pos secs :=
  posVal_accSum i pos secs pos 0 (Nat.add_zero pos)

/-- Flapjack structural infrastructure generalizes the physical starting
position for induction. It has no separately named original HOL declaration. -/
private theorem posVal_prefix {width : Nat} [NeZero width]
    (pc pos : Nat) (code suffix : LabProgHOL width) :
    pc < numPcs code → posVal pc pos (code ++ suffix) = posVal pc pos code := by
  induction code generalizing pc pos with
  | nil => simp [numPcs]
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    induction lines generalizing pc pos with
    | nil => simpa only [numPcs,posVal,List.cons_append] using ih pc pos
    | cons line lines ihLines =>
      cases line with
      | label a b len =>
        simpa only [numPcs,posVal,List.cons_append,isLabelHOL,↓reduceIte,lineLength]
          using ihLines pc (pos + (if len = 0 then 0 else 1))
      | asm a bytes len =>
        cases pc with
        | zero => simp [posVal,isLabelHOL]
        | succ pc =>
          intro h
          have hp : pc < numPcs (⟨sid,lines⟩::rest) := by
            simp only [numPcs,isLabelHOL,Bool.false_eq_true,↓reduceIte] at h
            omega
          simpa only [posVal,List.cons_append,isLabelHOL,Bool.false_eq_true,
            ↓reduceIte,Nat.succ_ne_zero,Nat.add_one_sub_one,lineLength]
            using ihLines pc (pos + bytes.length) hp
      | labAsm a w bytes len =>
        cases pc with
        | zero => simp [posVal,isLabelHOL]
        | succ pc =>
          intro h
          have hp : pc < numPcs (⟨sid,lines⟩::rest) := by
            simp only [numPcs,isLabelHOL,Bool.false_eq_true,↓reduceIte] at h
            omega
          simpa only [posVal,List.cons_append,isLabelHOL,Bool.false_eq_true,
            ↓reduceIte,Nat.succ_ne_zero,Nat.add_one_sub_one,lineLength]
            using ihLines pc (pos + bytes.length) hp

/-- Full original strict-prefix equation. The suffix is unrestricted, including
nonzero label annotations; no suffix validity or zero-label guard is added. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_APPEND1" (words_as_type_indexed_bitvec)]
theorem posVal_appendPrefix {width : Nat} [NeZero width]
    (pc : Nat) (code suffix : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    pc < numPcs code → posVal pc 0 (code ++ suffix) = posVal pc 0 code :=
  posVal_prefix pc 0 code suffix

/-- Flapjack structural infrastructure connecting the faithful instruction
count to a section boundary; no independently named original is claimed. -/
private theorem numPcs_section {width : Nat} [NeZero width]
    (sid : Nat) (lines : List (LabLineHOL width)) (rest : LabProgHOL width) :
    numPcs (⟨sid,lines⟩::rest) = lenNoLab lines + numPcs rest := by
  induction lines with
  | nil => simp [numPcs,lenNoLab]
  | cons line lines ih =>
    cases line <;> simp [numPcs,lenNoLab,isLabelHOL] at * <;> omega

/-- Flapjack section-boundary induction transports arbitrary physical starts
through unrestricted prefixes. This strengthening has no separate HOL name. -/
private theorem posVal_suffix {width : Nat} [NeZero width]
    (pc start : Nat) (code suffix : LabProgHOL width) :
    posVal (pc + numPcs code) start (code ++ suffix) =
      posVal pc (start + (code.map (fun sec => (sec.lines.map lineLength).sum)).sum) suffix := by
  induction code generalizing start with
  | nil => simp [numPcs]
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    rw [numPcs_section,List.cons_append,posVal_decompose]
    dsimp only
    have hex := secPosVal_tooBig (pc + (lenNoLab lines + numPcs rest)) start lines (by omega)
    rw [hex]
    have hsub : pc + (lenNoLab lines + numPcs rest) - lenNoLab lines = pc + numPcs rest := by omega
    rw [hsub,ih]
    simp only [List.map_cons,List.sum_cons,Nat.add_assoc]

/-- Full original suffix equation, with encoding validity required only of the
prefix at its independent start position. The suffix is entirely unrestricted;
physical-byte length is derived rather than assumed. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_APPEND2" (words_as_type_indexed_bitvec)]
theorem posVal_appendSuffix {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (p : Nat) (code : List (Section
      (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pc : Nat) (suffix : LabProgHOL width) :
    allEncOk c labs ffis p code →
    posVal (pc + numPcs code) 0 (code ++ suffix) =
      (progToBytes code).length + posVal pc 0 suffix := by
  intro h
  rw [posVal_suffix,allEncOk_lengthProgToBytes code () c labs ffis p h,Nat.zero_add]
  exact (posVal_accZero pc (progToBytes code).length suffix).symm
end Flapjack.Compiler.Backend.LabToTarget
