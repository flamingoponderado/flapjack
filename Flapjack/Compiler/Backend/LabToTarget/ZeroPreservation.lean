import Flapjack.Compiler.Backend.LabToTarget.SimpleEncoder
import Flapjack.Compiler.Backend.LabToTarget.PositionAppend
import Flapjack.Compiler.Backend.LabToTarget.Padding
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyLabelZero_addNop {width : Nat} [NeZero width]
    (xs : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (nop : List (BitVec 8)) :
    (∀ line ∈ addNop nop xs, labelZero line) ↔ (∀ line ∈ xs, labelZero line) := by
  induction xs with
  | nil => simp [addNop]
  | cons x xs ih => cases x <;> simp_all [addNop,labelZero]

/-- Unrestricted source lines: padding resets every new label; only old accumulator labels need the original premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyLabelZero_padSection {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (xs aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ aux, labelZero line) → ∀ line ∈ padSection nop xs aux, labelZero line := by
  induction xs generalizing aux with
  | nil => simp [padSection]
  | cons x xs ih =>
    intro h
    cases x with
    | label k1 k2 len =>
      simp only [padSection]
      apply ih
      by_cases hz : len = 0
      · simp_all [labelZero]
      · simpa [hz,labelZero] using (everyLabelZero_addNop aux nop).mpr h
    | asm a bs len =>
      simp only [padSection]
      apply ih
      simpa [labelZero] using h
    | labAsm a w bs len =>
      simp only [padSection]
      apply ih
      simpa [labelZero] using h

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everySecLabelZero_padCode {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    ∀ sec ∈ padCode nop ls, secLabelZero sec := by
  induction ls with
  | nil => simp [padCode]
  | cons sec ls ih =>
    rcases sec with ⟨id,lines⟩
    have hl := everyLabelZero_padSection nop lines [] (by simp)
    simpa [padCode,secLabelZero] using And.intro hl ih

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encLinesAgainSimp_labelZero {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (ls res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    encLinesAgainSimp labs ffis pos enc ls = (res,ok) ∧
      (∀ line ∈ ls, labelZero line) →
    ∀ line ∈ res, labelZero line := by
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
      simp_all [labelZero]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encSecsAgain_labelZero {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc lines = (res,ok) ∧
      (∀ sec ∈ lines, secLabelZero sec) →
    ∀ sec ∈ res, secLabelZero sec := by
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
    have hfirst := encLinesAgainSimp_labelZero labs ffis pos enc ls ls' flag
      ⟨hl,hls ⟨id,ls⟩ (by simp)⟩
    have htail := ih _ rest flag' ⟨hr,fun sec hm => hls sec (by simp [hm])⟩
    simpa [secLabelZero] using And.intro hfirst htail

end Flapjack.Compiler.Backend.LabToTarget
