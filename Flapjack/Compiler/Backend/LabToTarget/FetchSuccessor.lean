import Flapjack.Compiler.Backend.LabToTarget.PositionExtension
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original zero-position law. The encoding-validity start and queried
physical start remain independent, with no bounds or encoder-validity premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_0_aux" (words_as_type_indexed_bitvec)]
theorem posVal_zeroAt {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pos : Nat) :
    allEncOk c labs ffis validPos code → posVal 0 pos code = pos := by
  intro h
  exact secLabelZero_posVal_zero code pos
    (allEncOk_implies_secLabelZero c labs ffis validPos code h)

/-- Full original fetched-instruction successor equation. Literal successful
source fetch and complete encoding validity are its only guards. Encoding
validity is checked at validPos independently of the arbitrary queried pos. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "asm_fetch_aux_pos_val_SUC" (words_as_type_indexed_bitvec)]
theorem asmFetchAux_posVal_successor {width : Nat} [NeZero width]
    (pc pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (validPos : Nat)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (fetched : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    allEncOk c labs ffis validPos code ∧ asmFetchAux pc code = some fetched →
    (lineBytes fetched).length + posVal pc pos code = posVal (pc+1) pos code := by
  induction code generalizing pc pos validPos with
  | nil => rintro ⟨_,hf⟩; simp [asmFetchAux] at hf
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    induction lines generalizing pc pos validPos with
    | nil =>
      rintro ⟨he,hf⟩
      have ht : allEncOk c labs ffis validPos rest := by
        have heParts := (allEncOk_cons c labs ffis [] validPos sid rest).mp he
        simpa only [List.map_nil,List.sum_nil,Nat.add_zero] using heParts.1
      have hfTail : asmFetchAux pc rest = some fetched := by
        simpa only [asmFetchAux] using hf
      simpa only [posVal] using ih pc pos validPos ⟨ht,hfTail⟩
    | cons head lines ihLines =>
      rintro ⟨he,hf⟩
      have hparts : lineOk c labs ffis validPos head ∧
          allEncOk c labs ffis (validPos + lineLength head) (⟨sid,lines⟩::rest) := by
        rw [allEncOk] at he
        exact he
      cases head with
      | label a b len =>
        have hfTail : asmFetchAux pc (⟨sid,lines⟩::rest) = some fetched := by
          simpa only [asmFetchAux,isLabelHOL,↓reduceIte] using hf
        simpa only [posVal,isLabelHOL,↓reduceIte,lineLength] using
          ihLines pc (pos + (if len=0 then 0 else 1))
            (validPos + (if len=0 then 0 else 1)) ⟨hparts.2,hfTail⟩
      | asm a bytes len =>
        cases pc with
        | zero =>
          have heq : fetched = .asm a bytes len :=
            (Option.some.inj (by simpa [asmFetchAux,isLabelHOL] using hf)).symm
          subst fetched
          simp only [posVal,isLabelHOL,Bool.false_eq_true,↓reduceIte,Nat.reduceAdd,
            lineLength,lineBytes,Nat.add_one_sub_one]
          change bytes.length + pos = posVal 0 (pos + bytes.length) (⟨sid,lines⟩::rest)
          rw [posVal_zeroAt c labs ffis (validPos + bytes.length) _ _ hparts.2]
          omega
        | succ pc =>
          have hfTail : asmFetchAux pc (⟨sid,lines⟩::rest) = some fetched := by
            simpa [asmFetchAux,isLabelHOL] using hf
          simpa [posVal,isLabelHOL,lineLength] using
            ihLines pc (pos + bytes.length) (validPos + bytes.length) ⟨hparts.2,hfTail⟩
      | labAsm a w bytes len =>
        cases pc with
        | zero =>
          have heq : fetched = .labAsm a w bytes len :=
            (Option.some.inj (by simpa [asmFetchAux,isLabelHOL] using hf)).symm
          subst fetched
          simp only [posVal,isLabelHOL,Bool.false_eq_true,↓reduceIte,Nat.reduceAdd,
            lineLength,lineBytes,Nat.add_one_sub_one]
          change bytes.length + pos = posVal 0 (pos + bytes.length) (⟨sid,lines⟩::rest)
          rw [posVal_zeroAt c labs ffis (validPos + bytes.length) _ _ hparts.2]
          omega
        | succ pc =>
          have hfTail : asmFetchAux pc (⟨sid,lines⟩::rest) = some fetched := by
            simpa [asmFetchAux,isLabelHOL] using hf
          simpa [posVal,isLabelHOL,lineLength] using
            ihLines pc (pos + bytes.length) (validPos + bytes.length) ⟨hparts.2,hfTail⟩
end Flapjack.Compiler.Backend.LabToTarget
