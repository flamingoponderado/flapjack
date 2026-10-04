import Flapjack.Compiler.Backend.LabToTarget.SimpleEncoder

/-! Full original 0/1 label-annotation establishment and preservation.
The label update establishes the invariant for unrestricted input lines;
repeated encoding preserves it for either value of the returned flag. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def labelOne {width : Nat} [NeZero width] : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → Prop
  | .label _ _ n => n ≤ 1
  | _ => True

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secLabelOne {width : Nat} [NeZero width] (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  ∀ line ∈ sec.lines, labelOne line

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem linesUpdLabLen_labelOne {width : Nat} [NeZero width]
    (pos : Nat) (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ acc, labelOne line) →
      ∀ line ∈ (linesUpdLabLen pos ls acc).1, labelOne line := by
  fun_induction linesUpdLabLen pos ls acc <;> simp_all [labelOne]
  rename_i l1 hih
  have hl : l1 ≤ 1 := by dsimp [l1]; split <;> decide
  exact hih hl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem updLabLen_labelOne {width : Nat} [NeZero width]
    (pos : Nat) (ss : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    ∀ sec ∈ updLabLen pos ss, secLabelOne sec := by
  induction ss generalizing pos with
  | nil => simp [updLabLen]
  | cons sec rest ih =>
    rcases sec with ⟨id,lines⟩
    have hl := linesUpdLabLen_labelOne pos lines [] (by simp)
    have hr := ih (linesUpdLabLen pos lines []).2
    simpa [updLabLen,secLabelOne] using And.intro hl hr

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encLinesAgainSimp_labelOne {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (ls res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    encLinesAgainSimp labs ffis pos enc ls = (res,ok) ∧
      (∀ line ∈ ls, labelOne line) →
    ∀ line ∈ res, labelOne line := by
  induction ls generalizing pos res ok with
  | nil => rintro ⟨heq,_⟩; simp only [encLinesAgainSimp,Prod.mk.injEq] at heq; rcases heq with ⟨heq,_⟩; subst res; simp
  | cons line tail ih =>
    rintro ⟨heq,hls⟩
    cases line <;> simp only [encLinesAgainSimp] at heq
    all_goals try split at heq
    all_goals
      generalize hr : encLinesAgainSimp labs ffis _ enc tail = result at heq
      rcases result with ⟨rest,flag⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨hres,hflag⟩
      subst res
      have ht := ih _ rest flag ⟨hr, fun l hm => hls l (by simp [hm])⟩
      simp_all [labelOne]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encSecsAgain_labelOne {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc lines = (res,ok) ∧
      (∀ sec ∈ lines, secLabelOne sec) →
    ∀ sec ∈ res, secLabelOne sec := by
  induction lines generalizing pos res ok with
  | nil => rintro ⟨heq,_⟩; simp only [encSecsAgain,Prod.mk.injEq] at heq; rcases heq with ⟨heq,_⟩; subst res; simp
  | cons sec tail ih =>
    rcases sec with ⟨id,ls⟩
    rintro ⟨heq,hls⟩
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
    have hfirst := encLinesAgainSimp_labelOne labs ffis pos enc ls ls' flag
      ⟨hl,hls ⟨id,ls⟩ (by simp)⟩
    have htail := ih _ rest flag' ⟨hr,fun sec hm => hls sec (by simp [hm])⟩
    simpa [secLabelOne] using And.intro hfirst htail

end Flapjack.Compiler.Backend.LabToTarget
