import Flapjack.Compiler.Backend.LabToTarget.LabelPosition
import Flapjack.Compiler.Backend.LabToTarget.SimpleEncoder
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Original successful repeated-encoding preservation, with precisely the
source result equality and input parity conjunct. No encoder-validity premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_pos_ok"
  (words_as_type_indexed_bitvec)]
theorem encLinesAgainSimp_posOk {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    encLinesAgainSimp labs ffis pos enc lines = (res,true) ∧ labLenPosOk pos lines →
      labLenPosOk pos res := by
  induction lines generalizing pos res with
  | nil =>
    rintro ⟨heq,_⟩
    have hr : res = [] := (Prod.mk.inj heq).1.symm
    subst res
    exact True.intro
  | cons line tail ih =>
    rintro ⟨heq,hpos⟩
    cases line <;> simp only [encLinesAgainSimp] at heq
    all_goals try split at heq
    all_goals
      generalize hr : encLinesAgainSimp labs ffis _ enc tail = result at heq
      rcases result with ⟨rest,flag⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨hres,hflag⟩
      subst res
      simp only [labLenPosOk,lineLabLenPosOk,lineLen] at hpos ⊢
      try simp only [Bool.and_eq_true, decide_eq_true_eq] at hflag
      first
      | exact ⟨hpos.1,ih _ rest ⟨hr.trans (congrArg (Prod.mk rest) hflag),hpos.2⟩⟩
      | rw [hflag.1] at hr ⊢
        exact ⟨hpos.1,ih _ rest ⟨hr.trans (congrArg (Prod.mk rest) hflag.2),hpos.2⟩⟩

/-- Full original successful section encoding preserves input label parity.
The original simple-encoder agreement and length law identify its next position. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_pos_ok"
  (words_as_type_indexed_bitvec)]
theorem encSecsAgain_posOk {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (code res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    encSecsAgain pos labs ffis enc code = (res,true) ∧ allLabLenPosOk pos code →
      allLabLenPosOk pos res := by
  induction code generalizing pos res with
  | nil =>
    rintro ⟨heq,_⟩
    have hr : res = [] := (Prod.mk.inj heq).1.symm
    subst res
    exact True.intro
  | cons sec rest ih =>
    rcases sec with ⟨id,lines⟩
    rintro ⟨heq,hpos⟩
    simp only [encSecsAgain] at heq
    rw [encLinesAgainSimp_eq labs ffis pos enc lines [] true] at heq
    generalize hl : encLinesAgainSimp labs ffis pos enc lines = lr at heq
    rcases lr with ⟨lines1,flag⟩
    simp only [List.reverse_nil,List.nil_append,Bool.true_and] at heq
    generalize ht : encSecsAgain (secLength lines1 pos) labs ffis enc rest = tr at heq
    rcases tr with ⟨rest1,flag1⟩
    simp only [Prod.mk.injEq,Bool.and_eq_true] at heq
    rcases heq with ⟨hres,hflag,hflag1⟩
    subst res
    have hltrue := hl.trans (congrArg (Prod.mk lines1) hflag)
    have httrue := ht.trans (congrArg (Prod.mk rest1) hflag1)
    have hlen := encLinesAgainSimp_len labs ffis pos enc lines lines1 hltrue
    simp only [allLabLenPosOk] at hpos ⊢
    refine ⟨encLinesAgainSimp_posOk labs ffis pos enc lines lines1 ⟨hltrue,hpos.1⟩,?_⟩
    have hrest := ih (secLength lines1 pos) rest1 ⟨httrue,?_⟩
    · simpa [secLengthSumLineLen,Nat.add_comm] using hrest
    · simpa [secLengthSumLineLen,hlen,Nat.add_comm] using hpos.2

end Flapjack.Compiler.Backend.LabToTarget
