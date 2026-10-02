import Flapjack.Compiler.Backend.LabToTarget.OffsetInvariant
import Flapjack.Compiler.Backend.LabToTarget.SimpleEncoder
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original unconditional offset establishment: the actual result equality
is the sole premise and the returned flag is arbitrary, including false. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_offset_ok"
  (words_as_type_indexed_bitvec)]
theorem encLinesAgainSimp_offsetOk {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) (lines res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    encLinesAgainSimp labs ffis pos enc lines = (res,ok) → linesOffsetOk labs ffis pos res := by
  induction lines generalizing pos res ok with
  | nil =>
    intro heq
    have hr : res = [] := (Prod.mk.inj heq).1.symm
    subst res
    exact True.intro
  | cons line tail ih =>
    intro heq
    cases line <;> simp only [encLinesAgainSimp] at heq
    all_goals try split at heq
    all_goals
      generalize hr : encLinesAgainSimp labs ffis _ enc tail = result at heq
      rcases result with ⟨rest,flag⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨hres,_⟩
      subst res
      simp only [linesOffsetOk,lineOffsetOk,lineLen]
      exact ⟨by first | assumption | rfl | trivial,ih _ rest flag hr⟩

/-- Full original section establishment uses the actual returned position from
accumulator/simple encoder agreement, with no successful flag assumption. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_offset_ok"
  (words_as_type_indexed_bitvec)]
theorem encSecsAgain_offsetOk {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (code res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc code = (res,ok) → offsetOk labs ffis pos res := by
  induction code generalizing pos res ok with
  | nil =>
    intro heq
    have hr : res = [] := (Prod.mk.inj heq).1.symm
    subst res
    exact True.intro
  | cons sec rest ih =>
    rcases sec with ⟨id,lines⟩
    intro heq
    simp only [encSecsAgain] at heq
    rw [encLinesAgainSimp_eq labs ffis pos enc lines [] true] at heq
    generalize hl : encLinesAgainSimp labs ffis pos enc lines = lr at heq
    rcases lr with ⟨lines1,flag⟩
    simp only [List.reverse_nil,List.nil_append,Bool.true_and] at heq
    generalize ht : encSecsAgain (secLength lines1 pos) labs ffis enc rest = tr at heq
    rcases tr with ⟨rest1,flag1⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨hres,_⟩
    subst res
    simp only [offsetOk]
    refine ⟨encLinesAgainSimp_offsetOk labs ffis pos enc lines lines1 flag hl,?_⟩
    have hrest := ih (secLength lines1 pos) rest1 flag1 ht
    simpa [secLengthSumLineLen,Nat.add_comm] using hrest
end Flapjack.Compiler.Backend.LabToTarget
