import Flapjack.Compiler.Backend.ClosToBvl.Prepared
import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants

/-! Label bounds for chained top-level closure expressions. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The labels assigned by chaining occupy the reserved top-level interval,
including its single dummy entry when the expression list is empty. -/
theorem chainExps_label_bounds (start : Nat) (expressions : List ClosLang.Exp)
    (label : Nat) (member : label ∈ (chainExps start expressions).map Prod.fst) :
    start ≤ label ∧ label < start + max 1 expressions.length := by
  induction expressions generalizing start with
  | nil =>
    simp [chainExps] at member
    subst label
    simp
  | cons first rest ih =>
    cases rest with
    | nil =>
      simp [chainExps] at member
      subst label
      simp
    | cons second tail =>
      simp only [chainExps, List.map_cons, List.mem_cons] at member
      cases member with
      | inl equal =>
        subst label
        simp
      | inr later =>
        have bounds := ih (start + 1) later
        simp only [List.length_cons] at bounds ⊢
        omega

/-- Chained top-level expressions have pairwise distinct entry labels. -/
theorem chainExps_labels_nodup (start : Nat) (expressions : List ClosLang.Exp) :
    ((chainExps start expressions).map Prod.fst).Nodup := by
  induction expressions generalizing start with
  | nil => simp [chainExps]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps]
    | cons second tail =>
      simp only [chainExps, List.map_cons, List.nodup_cons]
      constructor
      · intro member
        have bounds := chainExps_label_bounds (start + 1) (second :: tail) start member
        omega
      · exact ih (start + 1)

/-- Annotation retains the entry labels of a closure program. -/
theorem annotated_labels (program : List (Nat × Nat × ClosLang.Exp)) :
    (ClosAnnotate.compile program).map Prod.fst = program.map Prod.fst := by
  simp [ClosAnnotate.compile, List.map_map]

end Flapjack.Compiler.Backend.ClosToBvl
