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

/-- Decide exhaustiveness of a list of pattern rows. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_rows_def"]
def exhRows {α : Type} (rows : List (Pat × α)) : Bool := exhMatrix (orRows rows)

end Flapjack.Compiler.Backend.PatternExh
