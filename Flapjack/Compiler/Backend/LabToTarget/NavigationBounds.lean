import Flapjack.Compiler.Backend.LabToTarget.SectionNavigation

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps

/-- The original sole successful-lookup premise bounds the returned instruction
index by the number of non-label lines, including the implicit label zero. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem secLocToPc_bound {width : Nat} [NeZero width] (n : Nat)
    (xs : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (x : Nat) :
    secLocToPc n xs = some x → x ≤ lenNoLab xs := by
  induction xs generalizing x with
  | nil =>
    by_cases hn : n = 0 <;> simp [secLocToPc, hn, lenNoLab] <;> omega
  | cons line xs ih =>
    rw [secLocToPc_cons]
    split
    · intro h
      simp only [Option.some.injEq] at h
      subst x
      exact Nat.zero_le _
    · intro h
      cases line <;> simp only [isLabelHOL, Bool.false_eq_true, ↓reduceIte] at h
      all_goals cases hr : secLocToPc n xs <;> simp [hr] at h
      all_goals subst x
      all_goals have hb := ih _ hr
      all_goals simp [lenNoLab, isLabelHOL] at *
      all_goals omega

/-- Full whole-code bound with the original section-validity and successful
lookup conjuncts; the count includes every section, including duplicates. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem locToPc_bound {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (l1 l2 x : Nat) :
    (∀ sec ∈ code, secLabelsOk sec) ∧ locToPc l1 l2 code = some x →
    x ≤ (code.map (fun sec => lenNoLab sec.lines)).sum := by
  induction code generalizing x with
  | nil => simp [locToPc]
  | cons sec code ih =>
    rcases sec with ⟨sid, lines⟩
    rintro ⟨hok, hlookup⟩
    have htail : ∀ sec ∈ code, secLabelsOk sec :=
      fun sec h => hok sec (by simp [h])
    rw [locToPc_sections l1 l2 _ hok] at hlookup
    simp only [List.map_cons, List.sum_cons]
    by_cases hs : l1 = sid
    · subst sid
      simp only [↓reduceIte] at hlookup
      cases hr : secLocToPc l2 lines with
      | none =>
        simp only [hr] at hlookup
        cases ht : locToPc l1 l2 code <;> simp [ht] at hlookup
        subst x
        have hb := ih _ ⟨htail, ht⟩
        omega
      | some y =>
        simp only [hr, Option.some.injEq] at hlookup
        subst x
        have hb := secLocToPc_bound l2 lines y hr
        omega
    · simp only [hs, ↓reduceIte] at hlookup
      cases ht : locToPc l1 l2 code <;> simp [ht] at hlookup
      subst x
      have hb := ih _ ⟨htail, ht⟩
      omega

end Flapjack.Compiler.Backend.LabToTarget
