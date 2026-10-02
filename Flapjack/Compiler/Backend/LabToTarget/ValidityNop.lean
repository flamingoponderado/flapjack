import Flapjack.Compiler.Backend.LabToTarget.NopInvariant
import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_ok_line_enc_with_nop"
  (words_as_type_indexed_bitvec)]
theorem lineOk_lineEncWithNop {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineOk c labs ffis pos line → lineEncWithNop c.encode labs ffis pos line := by
  cases line with
  | label => exact fun h => h.2
  | asm => exact fun h => ⟨h.1, h.2.1⟩
  | labAsm a w bytes len =>
    cases a with
    | halt => simpa [lineOk,lineEncWithNop,BitVec.zero_sub] using
        (fun h : lineOk c labs ffis pos (.labAsm .halt w bytes len) => And.intro h.1 h.2.1)
    | install => simpa [lineOk,lineEncWithNop,BitVec.zero_sub] using
        (fun h : lineOk c labs ffis pos (.labAsm .install w bytes len) => And.intro h.1 h.2.1)
    | callFFI name => simpa [lineOk,lineEncWithNop,BitVec.zero_sub,Nat.add_comm] using
        (fun h : lineOk c labs ffis pos (.labAsm (.callFFI name) w bytes len) => And.intro h.1 h.2.1)
    | call label => simp [lineOk]
    | jump label =>
      cases label with
      | lab k1 k2 =>
        cases hl : labLookup k1 k2 labs with
        | none => simp [lineOk,getLabel,hl]
        | some target =>
          intro h
          simp only [lineOk,getLabel,hl] at h
          have hp := labLookup_implies_findPos k1 k2 labs target hl
          simpa [lineEncWithNop,labInst,BitVec.sub_eq_add_neg,hp] using
            And.intro h.1 h.2.1
    | jumpCmp cmp reg imm label =>
      cases label with
      | lab k1 k2 =>
        cases hl : labLookup k1 k2 labs with
        | none => simp [lineOk,getLabel,hl]
        | some target =>
          intro h
          simp only [lineOk,getLabel,hl] at h
          have hp := labLookup_implies_findPos k1 k2 labs target hl
          simpa [lineEncWithNop,labInst,BitVec.sub_eq_add_neg,hp] using
            And.intro h.1 h.2.1
    | locValue reg label =>
      cases label with
      | lab k1 k2 =>
        cases hl : labLookup k1 k2 labs with
        | none => simp [lineOk,getLabel,hl]
        | some target =>
          intro h
          simp only [lineOk,getLabel,hl] at h
          have hp := labLookup_implies_findPos k1 k2 labs target hl
          simpa [lineEncWithNop,labInst,BitVec.sub_eq_add_neg,hp] using
            And.intro h.1 h.2.1

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_ok_lines_enc_with_nop"
  (words_as_type_indexed_bitvec)]
theorem linesOk_linesEncWithNop {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesOk c labs ffis pos lines → linesEncWithNop c.encode labs ffis pos lines := by
  induction lines generalizing pos with
  | nil => simp [linesEncWithNop]
  | cons line rest ih =>
    rintro ⟨hl, hr⟩
    exact ⟨lineOk_lineEncWithNop c labs ffis pos line hl, ih _ hr⟩
end Flapjack.Compiler.Backend.LabToTarget
