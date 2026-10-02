import Flapjack.Compiler.Backend.LabToTarget.EncodingInvariant
import Flapjack.Compiler.Backend.LabToTarget.SimpleEncoder
import Flapjack.Compiler.Backend.LabToTarget.PositionAppend
import Flapjack.Compiler.Backend.LabToTarget.LineLength
import Flapjack.Compiler.Backend.LabProps.LineLength
import Flapjack.Compiler.Encoders.AsmProps.Encoding
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_aligned_def"
  (words_as_type_indexed_bitvec)]
def lineAligned {width : Nat} [NeZero width] (m : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Prop :=
  lineLen line % m = 0 ∧ lineLength line % m = 0

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_aligned_def"
  (words_as_type_indexed_bitvec)]
def secAligned {width : Nat} [NeZero width] (m : Nat) (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  ∀ line ∈ sec.lines, lineAligned m line

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_encd0_aligned"
  (words_as_type_indexed_bitvec)]
theorem allEncd0_aligned {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (enc : HolAsm width → List (BitVec 8))
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    encOk c ∧ enc = c.encode ∧ allEncd0 enc code ∧
      (∀ sec ∈ code, secLabelZero sec) →
    ∀ sec ∈ code, secAligned (enc (.inst .skip)).length sec := by
  rintro ⟨hc,rfl,he,hz⟩
  intro sec hm line hl
  have he := he sec hm line hl
  have hz := hz sec hm line hl
  cases line with
  | label k1 k2 len =>
    simp only [labelZero] at hz
    subst len
    simp [lineAligned,lineLen,lineLength]
  | asm a bs len =>
    rcases he with ⟨hb,hl⟩
    simp only [lineAligned,lineLen,lineLength,hl,← hb,← hc.1]
    exact ⟨(hc.2.1 _).1,(hc.2.1 _).1⟩
  | labAsm a w bs len =>
    rcases he with ⟨hb,_,w',hlen⟩
    simp only [lineAligned,lineLen,lineLength,hlen,← hb,← hc.1]
    exact ⟨(hc.2.1 _).1,(hc.2.1 _).1⟩

/-- Flapjack-specific arithmetic lemma: MAX selects one of two aligned lengths. -/
private theorem maxAligned (x y m : Nat) (hx : x % m = 0) (hy : y % m = 0) :
    max x y % m = 0 := by
  rw [Nat.max_def]
  split <;> assumption

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_aligned"
  (words_as_type_indexed_bitvec)]
theorem encLinesAgainSimp_aligned {width : Nat} [NeZero width]
    (len : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (ls res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    (∀ a, (enc a).length % len = 0) ∧
    encLinesAgainSimp labs ffis pos enc ls = (res,ok) ∧
      (∀ line ∈ ls, lineAligned len line) →
    ∀ line ∈ res, lineAligned len line := by
  induction ls generalizing pos res ok with
  | nil => rintro ⟨_,heq,_⟩; simp only [encLinesAgainSimp,Prod.mk.injEq] at heq; rcases heq with ⟨heq,_⟩; subst res; simp
  | cons line tail ih =>
    rintro ⟨henc,heq,hls⟩
    cases line <;> simp only [encLinesAgainSimp] at heq
    all_goals try split at heq
    all_goals
      generalize hr : encLinesAgainSimp labs ffis _ enc tail = result at heq
      rcases result with ⟨rest,flag⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨hres,hflag⟩
      subst res
      have ht := ih _ rest flag ⟨henc,hr, fun l hm => hls l (by simp [hm])⟩
      simp_all [lineAligned,lineLen,lineLength]
      try exact maxAligned _ _ len (henc _) hls.1.1

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_aligned"
  (words_as_type_indexed_bitvec)]
theorem encSecsAgain_aligned {width : Nat} [NeZero width]
    (len pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    (∀ a, (enc a).length % len = 0) ∧
    encSecsAgain pos labs ffis enc lines = (res,ok) ∧
      (∀ sec ∈ lines, secAligned len sec) →
    ∀ sec ∈ res, secAligned len sec := by
  induction lines generalizing pos res ok with
  | nil => rintro ⟨_,heq,_⟩; simp only [encSecsAgain,Prod.mk.injEq] at heq; rcases heq with ⟨heq,_⟩; subst res; simp
  | cons sec tail ih =>
    rcases sec with ⟨id,ls⟩
    rintro ⟨henc,heq,hls⟩
    simp only [encSecsAgain] at heq
    rw [encLinesAgainSimp_eq] at heq
    generalize hl : encLinesAgainSimp labs ffis pos enc ls = lr at heq
    rcases lr with ⟨ls',flag⟩
    simp only [List.reverse_nil,List.nil_append,Bool.true_and] at heq
    generalize hr : encSecsAgain (secLength ls' pos) labs ffis enc tail = rr at heq
    rcases rr with ⟨rest,flag'⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨hres,hflag⟩
    subst res
    have hfirst := encLinesAgainSimp_aligned len labs ffis pos enc ls ls' flag
      ⟨henc,hl,hls ⟨id,ls⟩ (by simp)⟩
    have htail := ih _ rest flag' ⟨henc,hr,fun sec hm => hls sec (by simp [hm])⟩
    simpa [secAligned] using And.intro hfirst htail

end Flapjack.Compiler.Backend.LabToTarget
