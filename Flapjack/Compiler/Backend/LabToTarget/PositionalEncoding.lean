import Flapjack.Compiler.Backend.LabToTarget.EncodingInvariant
import Flapjack.Compiler.Backend.LabToTarget.LabelAnnotations

/-! Complete original positional encoding invariants and byte-length bounds.
Position advances through recorded line annotations, including labels; section
positions use the sum of those annotations. Stored LabAsm words are ignored by
line_encd exactly as in the source. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_leq_def"
  (words_as_type_indexed_bitvec)]
def lineLengthLeq {width : Nat} [NeZero width] : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → Prop
  | .asm _ bytes len => bytes.length ≤ len
  | .labAsm _ _ bytes len => bytes.length ≤ len
  | .label _ _ _ => True

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_length_leq_def"
  (words_as_type_indexed_bitvec)]
def secLengthLeq {width : Nat} [NeZero width] (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  ∀ line ∈ sec.lines, lineLengthLeq line

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_length_leq"
  (words_as_type_indexed_bitvec)]
def allLengthLeq {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Prop :=
  ∀ sec ∈ code, secLengthLeq sec

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_encd_def"
  (words_as_type_indexed_bitvec)]
def lineEncd {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Prop :=
  match line with
  | .asm b bytes len => enc (cbwToAsmExact b) = bytes ∧ len = bytes.length
  | .labAsm .halt _ bytes len =>
      enc (.jump (-BitVec.ofNat width (pos + ffiOffset))) = bytes ∧ bytes.length ≤ len
  | .labAsm .install _ bytes len =>
      enc (.jump (-BitVec.ofNat width (pos + 2 * ffiOffset))) = bytes ∧ bytes.length ≤ len
  | .labAsm (.callFFI name) _ bytes len =>
      enc (.jump (-BitVec.ofNat width (pos + (getFfiIndex ffis (.extCall name) + 3) * ffiOffset))) = bytes ∧
        bytes.length ≤ len
  | .labAsm (.jump label) _ bytes len =>
      enc (.jump (BitVec.ofNat width (findPos label labs) + -BitVec.ofNat width pos)) = bytes ∧
        bytes.length ≤ len
  | .labAsm (.jumpCmp cmp reg imm label) _ bytes len =>
      enc (.jumpCmp cmp reg imm (BitVec.ofNat width (findPos label labs) + -BitVec.ofNat width pos)) = bytes ∧
        bytes.length ≤ len
  | .labAsm (.locValue reg label) _ bytes len =>
      enc (.loc reg (BitVec.ofNat width (findPos label labs) + -BitVec.ofNat width pos)) = bytes ∧
        bytes.length ≤ len
  | .labAsm (.call label) _ bytes len =>
      enc (.call (BitVec.ofNat width (findPos label labs) + -BitVec.ofNat width pos)) = bytes ∧
        bytes.length ≤ len
  | .label _ _ _ => True

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_encd_def"
  (words_as_type_indexed_bitvec)]
def linesEncd {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → Prop
  | [] => True
  | line :: rest => lineEncd enc labs ffis pos line ∧
      linesEncd enc labs ffis (pos + lineLen line) rest

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_encd_def"
  (words_as_type_indexed_bitvec)]
def allEncd {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) → Prop
  | [] => True
  | sec :: rest => linesEncd enc labs ffis pos sec.lines ∧
      allEncd enc labs ffis (pos + (sec.lines.map lineLen).sum) rest

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_encd_length_leq"
  (words_as_type_indexed_bitvec)]
theorem lineEncd_lengthLeq {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineEncd enc labs ffis pos line → lineLengthLeq line := by
  cases line with
  | label => simp [lineEncd,lineLengthLeq]
  | asm => simp [lineEncd,lineLengthLeq]; omega
  | labAsm a => cases a <;> simp [lineEncd,lineLengthLeq]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_encd_length_leq"
  (words_as_type_indexed_bitvec)]
theorem linesEncd_lengthLeq {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesEncd enc labs ffis pos ls → ∀ line ∈ ls, lineLengthLeq line := by
  induction ls generalizing pos with
  | nil => simp
  | cons line rest ih =>
    rintro ⟨hl,hr⟩
    simpa using And.intro (lineEncd_lengthLeq enc labs ffis pos line hl) (ih _ hr)

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_encd_length_leq"
  (words_as_type_indexed_bitvec)]
theorem allEncd_lengthLeq {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncd enc labs ffis pos ls → allLengthLeq ls := by
  induction ls generalizing pos with
  | nil => simp [allLengthLeq]
  | cons sec rest ih =>
    rintro ⟨hl,hr⟩
    have hf : secLengthLeq sec := linesEncd_lengthLeq enc labs ffis pos sec.lines hl
    simpa [allLengthLeq] using And.intro hf (ih _ hr)

/-- Proof factoring for the native offset definitions, with no separate HOL original. -/
private theorem lineEncd_labAsm {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat)
    (a : AsmWithLab HolCmp (HolRegImm width) MlString)
    (w : BitVec width) (bytes : List (BitVec 8)) (len : Nat) :
    lineEncd enc labs ffis pos (.labAsm a w bytes len) ↔
      enc (labInst (getJumpOffset a ffis labs pos) a) = bytes ∧ bytes.length ≤ len := by
  cases a <;> simp [lineEncd,labInst,getJumpOffset,getLabel,BitVec.sub_eq_add_neg,Nat.add_comm]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_encd"
  (words_as_type_indexed_bitvec)]
theorem encLinesAgainSimp_encd {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    encLinesAgainSimp labs ffis pos enc lines = (res,true) ∧
      (∀ line ∈ lines, labelOne line) ∧ (∀ line ∈ lines, lineEncd0 enc line) →
    linesEncd enc labs ffis pos res := by
  induction lines generalizing pos res with
  | nil =>
    rintro ⟨heq,_,_⟩
    simp only [encLinesAgainSimp,Prod.mk.injEq] at heq
    rcases heq with ⟨heq,_⟩
    subst res
    trivial
  | cons line tail ih =>
    rintro ⟨heq,hl,he⟩
    have hx := he line (by simp)
    have htL : ∀ l ∈ tail, labelOne l := fun l hm => hl l (by simp [hm])
    have htE : ∀ l ∈ tail, lineEncd0 enc l := fun l hm => he l (by simp [hm])
    cases line <;> simp only [encLinesAgainSimp] at heq
    all_goals try split at heq
    all_goals
      generalize hr : encLinesAgainSimp labs ffis _ enc tail = result at heq
      rcases result with ⟨rest,flag⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨hres,hflag⟩
      subst res
      try simp only [Bool.and_eq_true,decide_eq_true_eq] at hflag
      have hf : flag = true := by first | exact hflag | exact hflag.2
      have ht := ih _ rest ⟨hr.trans (congrArg (Prod.mk rest) hf),htL,htE⟩
      simp only [linesEncd,lineLen]
    · exact ⟨trivial,ht⟩
    · exact ⟨hx,ht⟩
    · constructor
      · rw [lineEncd_labAsm]
        simpa only [← ‹_ = getJumpOffset _ _ _ _›] using And.intro hx.1 hx.2.1
      · exact ht
    · constructor
      · rw [lineEncd_labAsm]
        exact ⟨rfl,Nat.le_max_left _ _⟩
      · exact ht

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_encd"
  (words_as_type_indexed_bitvec)]
theorem encSecsAgain_encd {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (ls res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    encSecsAgain pos labs ffis enc ls = (res,true) ∧
      (∀ sec ∈ ls, secLabelOne sec) ∧ (∀ sec ∈ ls, secEncd0 enc sec) →
    allEncd enc labs ffis pos res := by
  induction ls generalizing pos res with
  | nil =>
    rintro ⟨heq,_,_⟩
    simp only [encSecsAgain,Prod.mk.injEq] at heq
    rcases heq with ⟨heq,_⟩
    subst res
    trivial
  | cons sec tail ih =>
    rcases sec with ⟨id,lines⟩
    rintro ⟨heq,hl,he⟩
    simp only [encSecsAgain] at heq
    rw [encLinesAgainSimp_eq] at heq
    generalize hlines : encLinesAgainSimp labs ffis pos enc lines = lr at heq
    rcases lr with ⟨lines',flag⟩
    simp only [List.reverse_nil,List.nil_append,Bool.true_and] at heq
    generalize hrest : encSecsAgain (secLength lines' pos) labs ffis enc tail = rr at heq
    rcases rr with ⟨rest,flag'⟩
    simp only [Prod.mk.injEq,Bool.and_eq_true] at heq
    rcases heq with ⟨hres,hflag,hflag'⟩
    subst res
    have hfirst := encLinesAgainSimp_encd labs ffis pos enc lines lines'
      ⟨hlines.trans (congrArg (Prod.mk lines') hflag),hl ⟨id,lines⟩ (by simp),he ⟨id,lines⟩ (by simp)⟩
    have htail := ih _ rest
      ⟨hrest.trans (congrArg (Prod.mk rest) hflag'),
       fun sec hm => hl sec (by simp [hm]), fun sec hm => he sec (by simp [hm])⟩
    simpa only [allEncd,secLengthSumLineLen,Nat.add_comm] using And.intro hfirst htail

end Flapjack.Compiler.Backend.LabToTarget
