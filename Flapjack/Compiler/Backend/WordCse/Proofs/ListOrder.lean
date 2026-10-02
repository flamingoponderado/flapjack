import Flapjack.Compiler.Backend.WordCse.ListOrder

namespace Flapjack.Compiler.Backend.WordCse

/-- Full original equality characterisation, without sortedness or bounds. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "listCmpEq_correct"]
theorem listCmpEqCorrect (x y : List Nat) : listCmp x y = .eq ↔ x = y := by
  induction x generalizing y with
  | nil => cases y <;> simp [listCmp]
  | cons a xs ih =>
    cases y with
    | nil => simp [listCmp]
    | cons b ys =>
      by_cases h : a = b
      · subst b; simp [listCmp, ih]
      · simp [listCmp, h]; split <;> simp

/-- Full original comparison reversal for arbitrary lists. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "antisym_listCmp"]
theorem antisymListCmp (x y : List Nat) : listCmp x y = .gt ↔ listCmp y x = .lt := by
  induction x generalizing y with
  | nil => cases y <;> simp [listCmp]
  | cons a xs ih =>
    cases y with
    | nil => simp [listCmp]
    | cons b ys =>
      by_cases h : a = b
      · subst b; simp [listCmp, ih]
      · have hba : b ≠ a := Ne.symm h
        simp only [listCmp, h, hba, if_false]
        split <;> split <;> simp_all <;> omega

/-- Full original strict transitivity with exactly the two comparison premises. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "transit_listCmp"]
theorem transitListCmp (x y z : List Nat)
    (h : listCmp x y = .lt ∧ listCmp y z = .lt) : listCmp x z = .lt := by
  induction x generalizing y z with
  | nil => cases y <;> cases z <;> simp_all [listCmp]
  | cons a xs ih =>
    cases y with
    | nil => simp [listCmp] at h
    | cons b ys =>
      cases z with
      | nil => simp [listCmp] at h
      | cons c zs =>
        by_cases hab : a = b
        · subst b
          by_cases hac : a = c
          · subst c; simp only [listCmp, ↓reduceIte] at h ⊢; exact ih ys zs h
          · simpa [listCmp, hac] using h.2
        · by_cases hbc : b = c
          · subst c; simpa [listCmp, hab] using h.1
          · have hablt : a < b := by
              by_cases hgt : a > b <;> simp [listCmp, hab, hgt] at h
              omega
            have hbclt : b < c := by
              by_cases hgt : b > c <;> simp [listCmp, hbc, hgt] at h
              omega
            have hac : a ≠ c := by omega
            have hgt : ¬ a > c := by omega
            simp [listCmp, hac, hgt]

/-- Flapjack infrastructure: unconditional agreement with Lean's previous
executed list comparator. There is no HOL declaration for Lean's `compare`. -/
theorem listCmpEqStdCompare (x y : List Nat) : listCmp x y = compare x y := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a xs ih =>
    cases y with
    | nil => rfl
    | cons b ys =>
      simp only [listCmp, List.compare_cons_cons]
      by_cases h : a = b
      · subst b; simp [ih]
      · by_cases hgt : a > b
        · simp [h, hgt, Nat.compare_eq_gt.mpr hgt]
        · have hlt : a < b := by omega
          simp [h, hgt, Nat.compare_eq_lt.mpr hlt]
/-- Function equality also covers comparator arguments passed to TreeMap,
rather than only fully applied comparator calls. No separate HOL original. -/
theorem listCmpFunctionEqStdCompare : listCmp = (compare : List Nat → List Nat → Ordering) :=
  funext fun x => funext fun y => listCmpEqStdCompare x y

end Flapjack.Compiler.Backend.WordCse
