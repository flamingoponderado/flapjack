import Flapjack.Compiler.Backend.LabToTarget.PositionExtension
import Flapjack.Compiler.Encoders.AsmProps.Encoding
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original successful-fetch instruction bound, with no encoding premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "asm_fetch_SOME_IMP_LESS_num_pcs" (words_as_type_indexed_bitvec)]
theorem asmFetchAux_some_ltNumPcs {width : Nat} [NeZero width]
    (pc : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (x : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    asmFetchAux pc code = some x → pc < numPcs code := by
  intro h
  by_cases hn : pc < numPcs code
  · exact hn
  have hb : numPcs code ≤ pc := by omega
  have hx := asmFetchAux_append2 (pc - numPcs code) code []
  have he : pc - numPcs code + numPcs code = pc := by omega
  rw [he,List.append_nil] at hx
  simp only [asmFetchAux] at hx
  rw [hx] at h
  contradiction

/-- Full original lower bound for arbitrary code and starting position. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_GE_pc" (words_as_type_indexed_bitvec)]
theorem posVal_geStart {width : Nat} [NeZero width]
    (i p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : p ≤ posVal i p code := by
  induction code generalizing i p with
  | nil => simp [posVal]
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    induction lines generalizing i p with
    | nil => simpa only [posVal] using ih i p
    | cons line lines ihLines =>
      cases line with
      | label a b len =>
        have h := ihLines i (p + (if len=0 then 0 else 1))
        simp only [posVal,isLabelHOL,↓reduceIte,lineLength]
        omega
      | asm a bytes len =>
        cases i with
        | zero => simp [posVal,isLabelHOL]
        | succ i =>
          have h := ihLines i (p + bytes.length)
          simpa only [posVal,isLabelHOL,Bool.false_eq_true,↓reduceIte,
            Nat.succ_ne_zero,Nat.add_one_sub_one,lineLength] using
            Nat.le_trans (Nat.le_add_right p bytes.length) h
      | labAsm a w bytes len =>
        cases i with
        | zero => simp [posVal,isLabelHOL]
        | succ i =>
          have h := ihLines i (p + bytes.length)
          simpa only [posVal,isLabelHOL,Bool.false_eq_true,↓reduceIte,
            Nat.succ_ne_zero,Nat.add_one_sub_one,lineLength] using
            Nat.le_trans (Nat.le_add_right p bytes.length) h

/-- Full original nonempty encoding consequence of complete enc_ok. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "enc_ok_LENGTH_GT_0" (words_as_type_indexed_bitvec)]
theorem encOk_lengthPositive {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (l : HolAsm width) :
    encOk c → 0 < (c.encode l).length := by
  intro h
  have hn := (h.2.1 l).2
  omega

/-- Full original instruction-count boundary equals emitted length; encoding
validity and queried physical starts are independent. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_num_pcs" (words_as_type_indexed_bitvec)]
theorem posVal_numPcs {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (p : Nat) :
    allEncOk c labs ffis validPos code →
    posVal (numPcs code) p code = p + (progToBytes code).length := by
  intro h
  have hx := posVal_appendSuffix c labs ffis validPos code 0 [] h
  simp only [Nat.zero_add,List.append_nil,posVal] at hx
  rw [←posVal_accZero, hx]
  simp

/-- Full original saturation beyond the instruction count. Code is unrestricted. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_GE_num_pcs" (words_as_type_indexed_bitvec)]
theorem posVal_geNumPcs {width : Nat} [NeZero width]
    (pc p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    numPcs code ≤ pc → posVal (numPcs code) p code = posVal pc p code := by
  induction code generalizing pc p with
  | nil => simp [posVal]
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    induction lines generalizing pc p with
    | nil => simpa only [posVal,numPcs] using ih pc p
    | cons line lines ihLines =>
      cases line with
      | label a b len =>
        simpa only [posVal,numPcs,isLabelHOL,↓reduceIte,lineLength] using
          ihLines pc (p + (if len=0 then 0 else 1))
      | asm a bytes len =>
        intro h
        have hb : numPcs (⟨sid,lines⟩::rest) ≤ pc-1 := by
          simp only [numPcs,isLabelHOL,Bool.false_eq_true,↓reduceIte] at h
          omega
        have hp : pc ≠ 0 := by
          simp only [numPcs,isLabelHOL,Bool.false_eq_true,↓reduceIte] at h
          omega
        simpa only [posVal,numPcs,isLabelHOL,Bool.false_eq_true,↓reduceIte,
          Nat.add_eq_zero_iff, Nat.one_ne_zero, false_and, hp,
          Nat.add_sub_cancel_left,lineLength] using ihLines (pc-1) (p+bytes.length) hb
      | labAsm a w bytes len =>
        intro h
        have hb : numPcs (⟨sid,lines⟩::rest) ≤ pc-1 := by
          simp only [numPcs,isLabelHOL,Bool.false_eq_true,↓reduceIte] at h
          omega
        have hp : pc ≠ 0 := by
          simp only [numPcs,isLabelHOL,Bool.false_eq_true,↓reduceIte] at h
          omega
        simpa only [posVal,numPcs,isLabelHOL,Bool.false_eq_true,↓reduceIte,
          Nat.add_eq_zero_iff, Nat.one_ne_zero, false_and, hp,
          Nat.add_sub_cancel_left,lineLength] using ihLines (pc-1) (p+bytes.length) hb

/-- Flapjack constructor infrastructure extracts nonempty emitted bytes from
actual line_ok and enc_ok. There is no independently named HOL original. -/
private theorem lineOk_nonempty {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (p : Nat) (line : LabLineHOL width) :
    lineOk c labs ffis p line → encOk c → isLabelHOL line = false →
    0 < lineLength line := by
  intro hl he hn
  have positive (inst : HolAsm width) (bytes : List (BitVec 8))
      (h : encWithNop c.encode inst bytes) : 0 < bytes.length := by
    obtain ⟨count, rfl⟩ := (encWithNop_iff c.encode inst bytes).mp h
    have hp := encOk_lengthPositive c inst he
    simp only [List.length_append]
    omega
  cases line with
  | label a b len => simp [isLabelHOL] at hn
  | asm a bytes len => exact positive _ bytes hl.1
  | labAsm a w bytes len =>
    cases a with
    | halt => exact positive _ bytes hl.1
    | install => exact positive _ bytes hl.1
    | callFFI idx => exact positive _ bytes hl.1
    | call lab => exact False.elim hl
    | jump lab =>
      cases lab with
      | lab a b =>
        simp only [lineOk,getLabel] at hl
        split at hl
        · contradiction
        · exact positive _ bytes hl.1
    | jumpCmp cmp r ri lab =>
      cases lab with
      | lab a b =>
        simp only [lineOk,getLabel] at hl
        split at hl
        · contradiction
        · exact positive _ bytes hl.1
    | locValue r lab =>
      cases lab with
      | lab a b =>
        simp only [lineOk,getLabel] at hl
        split at hl
        · contradiction
        · exact positive _ bytes hl.1

/-- Full original strict order, preserving both PC guards and the complete
encoding predicates at a start independent of the queried physical position. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_mono" (words_as_type_indexed_bitvec)]
theorem posVal_mono {width : Nat} [NeZero width]
    (i p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (j validPos : Nat)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName) :
    i < j ∧ j ≤ numPcs code ∧ allEncOk c labs ffis validPos code ∧ encOk c →
    posVal i p code < posVal j p code := by
  induction code generalizing i j p validPos with
  | nil => simp [numPcs]; omega
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    induction lines generalizing i j p validPos with
    | nil =>
      rintro ⟨hij,hj,he,hc⟩
      rw [allEncOk] at he
      have hjTail : j ≤ numPcs rest := by simpa only [numPcs] using hj
      simpa only [posVal] using ih i p j validPos ⟨hij,hjTail,he.2,hc⟩
    | cons line lines ihLines =>
      rintro ⟨hij,hj,he,hc⟩
      have hparts : lineOk c labs ffis validPos line ∧
          allEncOk c labs ffis (validPos + lineLength line) (⟨sid,lines⟩::rest) := by
        rw [allEncOk] at he
        exact he
      by_cases hl : isLabelHOL line = true
      · have hjTail : j ≤ numPcs (⟨sid,lines⟩::rest) := by
          simpa only [numPcs,hl,↓reduceIte] using hj
        simpa only [posVal,hl,↓reduceIte] using
          ihLines i (p + lineLength line) j (validPos + lineLength line)
            ⟨hij,hjTail,hparts.2,hc⟩
      · have hn : isLabelHOL line = false := Bool.eq_false_iff.mpr hl
        have hp := lineOk_nonempty c labs ffis validPos line hparts.1 hc hn
        cases i with
        | zero =>
          have hjn : j ≠ 0 := by omega
          simp only [posVal,hn,Bool.false_eq_true,↓reduceIte,hjn]
          have hg := posVal_geStart (j-1) (p + lineLength line) (⟨sid,lines⟩::rest)
          omega
        | succ i =>
          have hjn : j ≠ 0 := by omega
          have hlt : i < j-1 := by omega
          have hbound : j-1 ≤ numPcs (⟨sid,lines⟩::rest) := by
            simp only [numPcs,hn,Bool.false_eq_true,↓reduceIte] at hj
            omega
          simpa only [posVal,hn,Bool.false_eq_true,↓reduceIte,hjn,
            Nat.succ_ne_zero,Nat.add_one_sub_one] using
            ihLines i (p + lineLength line) (j-1) (validPos + lineLength line)
              ⟨hlt,hbound,hparts.2,hc⟩

/-- Full original inverse order: only the first PC is bounded by num_pcs. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_mono_inv" (words_as_type_indexed_bitvec)]
theorem posVal_monoInv {width : Nat} [NeZero width]
    (i p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (j : Nat)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) :
    posVal i p code < posVal j p code ∧ i ≤ numPcs code ∧
      allEncOk c labs ffis validPos code ∧ encOk c → i < j := by
  rintro ⟨hpos,hi,he,hc⟩
  by_cases hij : i < j
  · exact hij
  by_cases heq : i = j
  · subst j; omega
  have hji : j < i := by omega
  have hrev := posVal_mono j p code i validPos c labs ffis ⟨hji,hi,he,hc⟩
  omega

/-- Full original injectivity on the bounded instruction-count interval. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "pos_val_inj" (words_as_type_indexed_bitvec)]
theorem posVal_inj {width : Nat} [NeZero width]
    (i p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (j : Nat)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) :
    posVal i p code = posVal j p code ∧ i ≤ numPcs code ∧ j ≤ numPcs code ∧
      allEncOk c labs ffis validPos code ∧ encOk c → i = j := by
  rintro ⟨hpos,hi,hj,he,hc⟩
  by_cases hij : i < j
  · have hs := posVal_mono i p code j validPos c labs ffis ⟨hij,hj,he,hc⟩
    omega
  by_cases hji : j < i
  · have hs := posVal_mono j p code i validPos c labs ffis ⟨hji,hi,he,hc⟩
    omega
  omega
end Flapjack.Compiler.Backend.LabToTarget
