import Flapjack.Compiler.Backend.ClosToBvl.Prepared
import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants

/-! Label bounds for chained top-level closure expressions. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Chaining expressions preserves their closure-code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_code_locs"]
theorem chainExps_codeLocations (start : Nat) (expressions : List ClosLang.Exp) :
    ClosProps.codeLocations ((chainExps start expressions).map (fun (_, _, body) => body)) =
      ClosProps.codeLocations expressions := by
  induction expressions generalizing start with
  | nil => simp [chainExps, ClosProps.codeLocations, ClosProps.codeLocationsExp]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps, ClosProps.codeLocations]
    | cons second tail =>
      simpa [chainExps, ClosProps.codeLocations, ClosProps.codeLocationsExp] using
        congrArg (fun locations => ClosProps.codeLocationsExp first ++ locations) (ih (start + 1))

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

/-- Every generated entry label is at least the starting label. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_LE"]
theorem chainExps_le (start : Nat) (expressions : List ClosLang.Exp) :
    ∀ label ∈ (chainExps start expressions).map Prod.fst, start ≤ label := by
  intro label member
  exact (chainExps_label_bounds start expressions label member).1

/-- A nonempty chain stays below its starting label plus its length. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_GT"]
theorem chainExps_gt (start : Nat) (expressions : List ClosLang.Exp) :
    expressions ≠ [] →
    ∀ label ∈ (chainExps start expressions).map Prod.fst, label < start + expressions.length := by
  intro nonempty label member
  have bound := (chainExps_label_bounds start expressions label member).2
  cases expressions with
  | nil => exact (nonempty rfl).elim
  | cons first rest => simpa using bound

/-- Chained top-level expressions have pairwise distinct entry labels. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_ALL_DISTINCT"]
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
        have bounds := chainExps_le (start + 1) (second :: tail) start member
        omega
      · exact ih (start + 1)

/-- Annotation retains the entry labels of a closure program. -/
theorem annotated_labels (program : List (Nat × Nat × ClosLang.Exp)) :
    (ClosAnnotate.compile program).map Prod.fst = program.map Prod.fst := by
  simp [ClosAnnotate.compile, List.map_map]

end Flapjack.Compiler.Backend.ClosToBvl
