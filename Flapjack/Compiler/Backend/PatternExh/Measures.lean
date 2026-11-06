import Flapjack.Compiler.Backend.PatternExh.Weights

/-! Measure lemmas for the total exhaustiveness recursion. These reproduce the source termination lemmas; their statements
remain pending full typed HOL review. -/
namespace Flapjack.Compiler.Backend.PatternExh
open PatternSemantics

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pats_weight_append"]
theorem patsWeight_append (xs ys : List Pat) :
    patsWeight (xs ++ ys) = patsWeight xs + patsWeight ys := by
  induction xs with
  | nil => simp [patsWeight]
  | cons x xs ih => simp [patsWeight, ih, Nat.add_assoc]

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pats_weight_anys"]
theorem patsWeight_anys (n : Nat) : patsWeight (anys n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [anys, patsWeight, patWeight, ih]

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_weight_append"]
theorem matWeight_append (xs ys : List (List Pat)) :
    matWeight (xs ++ ys) = matWeight xs + matWeight ys := by
  induction xs with
  | nil => simp [matWeight]
  | cons x xs ih => simp [matWeight, ih, Nat.add_assoc]

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_len_append"]
theorem matLen_append (xs ys : List (List Pat)) :
    matLen (xs ++ ys) = matLen xs + matLen ys := by
  induction xs with
  | nil => simp [matLen]
  | cons x xs ih => simp [matLen, ih, Nat.add_assoc]

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_weight_spec_row"]
theorem matWeight_specRow_le (c : Ctor) (r : List Pat) :
    matWeight (specRow c r) ≤ patsWeight r := by
  cases r with
  | nil => simp [specRow, matWeight, patsWeight]
  | cons p rest =>
      cases p with
      | any => simp [specRow, matWeight, patsWeight, patWeight, patsWeight_append, patsWeight_anys]
      | lit l => simp [specRow, matWeight, patsWeight, patWeight]
      | or p q => simp [specRow, matWeight, patsWeight, patWeight]
      | ref p =>
          simp only [specRow, patsWeight, patWeight]
          split <;> simp [matWeight, patsWeight] <;> omega
      | cons tag ps =>
          cases tag with
          | none =>
              simp only [specRow, patsWeight, patWeight]
              split <;> simp [matWeight, patsWeight_append] <;> omega
          | some tag =>
              cases tag with
              | mk n siblings =>
                  simp only [specRow, patsWeight, patWeight]
                  split <;> simp [matWeight, patsWeight_append] <;> omega

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_weight_spec_mat"]
theorem matWeight_specMat_le (c : Ctor) (rows : List (List Pat)) :
    matWeight (specMat c rows) ≤ matWeight rows := by
  induction rows with
  | nil => simp [specMat, matWeight]
  | cons r rows ih =>
      simp only [specMat, matWeight_append, matWeight]
      have h := matWeight_specRow_le c r
      omega

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_weight_spec_row_less"]
theorem matWeight_specRow_lt (c : Ctor) (p : Pat) (rest : List Pat)
    (h : (ctorsOf p).isSome = true) :
    matWeight (specRow c (p :: rest)) < patsWeight (p :: rest) := by
  cases p with
  | any => simp [ctorsOf] at h
  | lit l => simp [ctorsOf] at h
  | or p q => simp [ctorsOf] at h
  | ref p =>
      simp only [specRow, patsWeight, patWeight]
      split <;> simp [matWeight, patsWeight] <;> omega
  | cons tag ps =>
      cases tag with
      | none =>
          simp only [specRow, patsWeight, patWeight]
          split <;> simp [matWeight, patsWeight_append] <;> omega
      | some tag =>
          cases tag with
          | mk n siblings =>
              cases siblings with
              | none => simp [ctorsOf] at h
              | some siblings =>
                  simp only [specRow, patsWeight, patWeight]
                  split <;> simp [matWeight, patsWeight_append] <;> omega

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_weight_spec_mat_less"]
theorem matWeight_specMat_lt (c : Ctor) (rows : List (List Pat))
    (cs : List Ctor) (h : colCtors rows = some cs) :
    matWeight (specMat c rows) < matWeight rows := by
  induction rows generalizing cs with
  | nil => simp [colCtors] at h
  | cons r rows ih =>
      cases r with
      | nil =>
          simp only [colCtors] at h
          have hs := ih cs h
          simpa [specMat, specRow, matWeight, patsWeight] using hs
      | cons p rest =>
          cases hp : ctorsOf p with
          | none =>
              have htail : colCtors rows = some cs := by simpa [colCtors, hp, ctorInter] using h
              have hs := ih cs htail
              have hr := matWeight_specRow_le c (p :: rest)
              simp only [specMat, matWeight_append, matWeight]
              omega
          | some known =>
              have hr := matWeight_specRow_lt c p rest (by simp [hp])
              have hs := matWeight_specMat_le c rows
              simp only [specMat, matWeight_append, matWeight]
              omega

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mats_weight_spec_mats"]
theorem matsWeight_specMats_lt (cs : List Ctor) (rows : List (List Pat))
    (known : List Ctor) (h : colCtors rows = some known) :
    matsWeight (specMats cs rows) < matWeight rows := by
  induction cs with
  | nil =>
      have hpos := matWeight_specMat_lt .refC rows known h
      simp only [specMats, matsWeight]
      omega
  | cons c cs ih =>
      have hc := matWeight_specMat_lt c rows known h
      simp only [specMats, matsWeight]
      omega

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_weight_default_mat"]
theorem matWeight_defaultMat_le (rows : List (List Pat)) :
    matWeight (defaultMat rows) ≤ matWeight rows := by
  induction rows with
  | nil => simp [defaultMat, matWeight]
  | cons r rows ih =>
      cases r with
      | nil => simp [defaultMat, defaultRow, matWeight] at *; omega
      | cons p rest =>
          cases p <;> simp [defaultMat, defaultRow, matWeight, patsWeight, patWeight] at * <;> omega

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_len_default_mat"]
theorem matLen_defaultMat_le (rows : List (List Pat)) :
    matLen (defaultMat rows) ≤ matLen rows := by
  induction rows with
  | nil => simp [defaultMat, matLen]
  | cons r rows ih =>
      cases r with
      | nil => simp [defaultMat, defaultRow, matLen] at *; omega
      | cons p rest =>
          cases p <;> simp [defaultMat, defaultRow, matLen] at * <;> omega

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mat_len_default_mat_less"]
theorem matLen_defaultMat_lt (r : List Pat) (rows : List (List Pat)) (h : r ≠ []) :
    matLen (defaultMat (r :: rows)) < matLen (r :: rows) := by
  have ih := matLen_defaultMat_le rows
  cases r with
  | nil => contradiction
  | cons p rest =>
      cases p <;> simp [defaultMat, defaultRow, matLen] at * <;> omega

end Flapjack.Compiler.Backend.PatternExh
