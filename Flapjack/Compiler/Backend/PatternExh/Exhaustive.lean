import Flapjack.Compiler.Backend.PatternExh.Measures

/-! Total exhaustiveness analysis using CakeML's lexicographic measure. -/
namespace Flapjack.Compiler.Backend.PatternExh
open PatternSemantics

mutual
/-- Decide exhaustiveness of a pattern matrix. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_matrix_def"]
def exhMatrix (rows : List (List Pat)) : Bool :=
  match rows with
  | [] => false
  | r :: rs =>
      if r.isEmpty then true
      else match _hcol : colCtors (r :: rs) with
        | none => exhMatrix (defaultMat (r :: rs))
        | some cs => exhMats (specMats cs (r :: rs))
termination_by (matWeight rows, matLen rows, 0)
decreasing_by
  · simp_wf
    have hw := matWeight_defaultMat_le (r :: rs)
    have hn : r ≠ [] := by intro h; subst r; simp_all
    have hl := matLen_defaultMat_lt r rs hn
    by_cases heq : matWeight (defaultMat (r :: rs)) = matWeight (r :: rs)
    · rw [← heq]
      apply Prod.Lex.right
      apply Prod.Lex.left
      exact hl
    · apply Prod.Lex.left
      omega
  · simp_wf
    apply Prod.Lex.left
    exact matsWeight_specMats_lt cs (r :: rs) cs _hcol

/-- Decide exhaustiveness for every matrix in the list. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_matrix_def"]
def exhMats (ms : List (List (List Pat))) : Bool :=
  match ms with
  | [] => true
  | m :: rest => exhMatrix m && exhMats rest
termination_by (matsWeight ms, matsLen ms, ms.length + 1)
decreasing_by
  · simp_wf
    simp only [matsWeight, matsLen]
    have hw : matWeight m ≤ max (matWeight m) (matsWeight rest) := Nat.le_max_left _ _
    have hl : matLen m ≤ max (matLen m) (matsLen rest) := Nat.le_max_left _ _
    by_cases heq : matWeight m = max (matWeight m) (matsWeight rest)
    · rw [← heq]
      by_cases hlen : matLen m = max (matLen m) (matsLen rest)
      · rw [← hlen]
        apply Prod.Lex.right
        apply Prod.Lex.right
        omega
      · apply Prod.Lex.right
        apply Prod.Lex.left
        omega
    · apply Prod.Lex.left
      omega
  · simp_wf
    simp only [matsWeight, matsLen]
    have hw : matsWeight rest ≤ max (matWeight m) (matsWeight rest) := Nat.le_max_right _ _
    have hl : matsLen rest ≤ max (matLen m) (matsLen rest) := Nat.le_max_right _ _
    by_cases heq : matsWeight rest = max (matWeight m) (matsWeight rest)
    · rw [← heq]
      by_cases hlen : matsLen rest = max (matLen m) (matsLen rest)
      · rw [← hlen]
        apply Prod.Lex.right
        apply Prod.Lex.right
        omega
      · apply Prod.Lex.right
        apply Prod.Lex.left
        omega
    · apply Prod.Lex.left
      omega
end

mutual
/-- Count the recursive steps needed to analyze a pattern matrix. This is
proof-side support for the source's worklist exhaustiveness algorithm. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_steps_def"]
def exhSteps (rows : List (List Pat)) : Nat :=
  match rows with
  | [] => 1
  | r :: rs =>
      if r.isEmpty then 1
      else match _hcol : colCtors (r :: rs) with
        | none => 1 + exhSteps (defaultMat (r :: rs))
        | some cs => 1 + exhStepsList (specMats cs (r :: rs))
termination_by (matWeight rows, matLen rows, 0)
decreasing_by
  · simp_wf
    have hw := matWeight_defaultMat_le (r :: rs)
    have hn : r ≠ [] := by intro h; subst r; simp_all
    have hl := matLen_defaultMat_lt r rs hn
    by_cases heq : matWeight (defaultMat (r :: rs)) = matWeight (r :: rs)
    · rw [← heq]
      apply Prod.Lex.right
      apply Prod.Lex.left
      exact hl
    · apply Prod.Lex.left
      omega
  · simp_wf
    apply Prod.Lex.left
    exact matsWeight_specMats_lt cs (r :: rs) cs _hcol


/-- Sum the recursive step counts of a list of pattern matrices. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_steps_def"]
def exhStepsList (ms : List (List (List Pat))) : Nat :=
  match ms with
  | [] => 0
  | m :: rest => exhSteps m + exhStepsList rest
termination_by (matsWeight ms, matsLen ms, ms.length + 1)
decreasing_by
  · simp_wf
    simp only [matsWeight, matsLen]
    have hw : matWeight m ≤ max (matWeight m) (matsWeight rest) := Nat.le_max_left _ _
    have hl : matLen m ≤ max (matLen m) (matsLen rest) := Nat.le_max_left _ _
    by_cases heq : matWeight m = max (matWeight m) (matsWeight rest)
    · rw [← heq]
      by_cases hlen : matLen m = max (matLen m) (matsLen rest)
      · rw [← hlen]
        apply Prod.Lex.right
        apply Prod.Lex.right
        omega
      · apply Prod.Lex.right
        apply Prod.Lex.left
        omega
    · apply Prod.Lex.left
      omega
  · simp_wf
    simp only [matsWeight, matsLen]
    have hw : matsWeight rest ≤ max (matWeight m) (matsWeight rest) := Nat.le_max_right _ _
    have hl : matsLen rest ≤ max (matLen m) (matsLen rest) := Nat.le_max_right _ _
    by_cases heq : matsWeight rest = max (matWeight m) (matsWeight rest)
    · rw [← heq]
      by_cases hlen : matsLen rest = max (matLen m) (matsLen rest)
      · rw [← hlen]
        apply Prod.Lex.right
        apply Prod.Lex.right
        omega
      · apply Prod.Lex.right
        apply Prod.Lex.left
        omega
    · apply Prod.Lex.left
      omega
end

/-- The step count of concatenated matrix lists is additive. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_steps_list_append"]
theorem exhStepsList_append (xs ys : List (List (List Pat))) :
    exhStepsList (xs ++ ys) = exhStepsList xs + exhStepsList ys := by
  induction xs with
  | nil => simp [exhStepsList]
  | cons x xs ih => simp [exhStepsList, ih, Nat.add_assoc]

/-- Check a worklist of pattern matrices using the source's step measure. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_all_def"]
def exhAll (ms : List (List (List Pat))) : Bool :=
  match ms with
  | [] => true
  | [] :: _ => false
  | (r :: rows) :: rest =>
      if _hrow : r.isEmpty then exhAll rest
      else match _hcol : colCtors (r :: rows) with
        | none => exhAll (defaultMat (r :: rows) :: rest)
        | some cs => exhAll (specMats cs (r :: rows) ++ rest)
termination_by exhStepsList ms
decreasing_by
  all_goals simp_wf
  all_goals simp_all [exhStepsList, exhSteps, exhStepsList_append]
  all_goals rw [_hcol]
  all_goals simp

/-- Exhaustiveness of concatenated matrix lists is conjunctive. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_mats_append"]
theorem exhMats_append (xs ys : List (List (List Pat))) :
    exhMats (xs ++ ys) = (exhMats xs && exhMats ys) := by
  induction xs with
  | nil => simp [exhMats]
  | cons x xs ih => simp [exhMats, ih, Bool.and_assoc]

/-- The worklist traversal agrees with the matrix-list checker. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_all_thm"]
theorem exhAll_correct (ms : List (List (List Pat))) : exhAll ms = exhMats ms := by
  induction ms using exhAll.induct with
  | case1 => simp [exhAll, exhMats]
  | case2 tail => simp [exhAll, exhMats, exhMatrix]
  | case3 r rows rest h ih => simpa [exhAll, exhMats, exhMatrix, h] using ih
  | case4 r rows rest h hc ih =>
    simp only [exhAll, exhMats, exhMatrix, h, Bool.false_eq_true, ↓reduceIte]
    rw [hc]
    simpa [exhMats] using ih
  | case5 r rows rest h cs hc ih =>
    simp only [exhAll, exhMats, exhMatrix, h, Bool.false_eq_true, ↓reduceIte]
    rw [hc]
    simpa [exhMats_append] using ih

/-- Decide exhaustiveness of a list of pattern rows. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_rows_def"]
def exhRows {α : Type} (rows : List (Pat × α)) : Bool := exhMatrix (orRows rows)

/-- The source row checker agrees with the worklist execution equation. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_rows_eq"]
theorem exhRows_eq {α : Type} (rows : List (Pat × α)) :
    exhRows rows = exhAll [orRows rows] := by
  simp [exhRows, exhAll_correct, exhMats]

/-- Executable form of `exhRows`, justified by `exhRows_eq`. -/
def exhRowsWorklist {α : Type} (rows : List (Pat × α)) : Bool :=
  exhAll [orRows rows]

/-- Compile the row checker with the source worklist execution equation. -/
@[csimp] theorem exhRows_eq_worklist : @exhRows = @exhRowsWorklist := by
  funext α rows
  exact exhRows_eq rows

end Flapjack.Compiler.Backend.PatternExh
