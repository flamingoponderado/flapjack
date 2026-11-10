module

public import Flapjack.Compiler.Backend.ClosToBvl.Prepared
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants

@[expose] public section

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

/-- Chained expression labels form the complete range, with one entry for an
empty expression list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "MAP_FST_chain_exps_any"]
theorem mapFst_chainExps_any (start : Nat) (exps : List ClosLang.Exp) :
    (chainExps start exps).map Prod.fst =
      (List.range (max 1 exps.length)).map (start + ·) := by
  induction exps generalizing start with
  | nil => simp [chainExps]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps]
    | cons second tail =>
      have step := ih (start + 1)
      simp only [chainExps, List.map_cons] at step ⊢
      simp only [List.length_cons] at step ⊢
      rw [Nat.max_eq_right (by omega : 1 ≤ tail.length + 1)] at step
      rw [Nat.max_eq_right (by omega : 1 ≤ tail.length + 1 + 1)]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Function.comp_def]
      congr 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step

/-- Every generated entry label is at least the starting label. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_LE"]
theorem chainExps_le (start : Nat) (expressions : List ClosLang.Exp) :
    ∀ label ∈ (chainExps start expressions).map Prod.fst, start ≤ label := by
  intro label member
  rw [mapFst_chainExps_any] at member
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  omega

/-- A nonempty chain stays below its starting label plus its length. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_GT"]
theorem chainExps_gt (start : Nat) (expressions : List ClosLang.Exp) :
    expressions ≠ [] →
    ∀ label ∈ (chainExps start expressions).map Prod.fst, label < start + expressions.length := by
  intro nonempty label member
  rw [mapFst_chainExps_any] at member
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
  have bound := List.mem_range.mp hi
  cases expressions with
  | nil => exact (nonempty rfl).elim
  | cons first rest => simp only [List.length_cons] at bound ⊢; omega

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

end Flapjack.Compiler.Backend.ClosToBvl
