import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationBounds
import Mathlib.Data.List.Nodup

/-! Distinctness of closure-code locations produced by numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

private theorem nodup_append_separated (left right : List Nat) (cut : Nat)
    (leftDistinct : left.Nodup) (rightDistinct : right.Nodup)
    (leftBelow : ∀ value ∈ left, value < cut)
    (rightAbove : ∀ value ∈ right, cut ≤ value) : (left ++ right).Nodup := by
  apply List.Nodup.append leftDistinct rightDistinct
  intro value leftMember rightMember
  have a := leftBelow value leftMember
  have b := rightAbove value rightMember
  omega

/-- Locations that are distinct and lie in a half-open numbering interval. -/
private def locationSegment (locations : List Nat) (lower upper : Nat) : Prop :=
  locations.Nodup ∧ ∀ location ∈ locations, lower ≤ location ∧ location < upper

private theorem locationSegment_append {left right : List Nat} {lower middle upper : Nat}
    (leftSegment : locationSegment left lower middle) (rightSegment : locationSegment right middle upper)
    (firstStep : lower ≤ middle) (secondStep : middle ≤ upper) :
    locationSegment (left ++ right) lower upper := by
  constructor
  · apply nodup_append_separated left right middle leftSegment.1 rightSegment.1
    · intro value member; exact (leftSegment.2 value member).2
    · intro value member; exact (rightSegment.2 value member).1
  · intro location member
    simp only [List.mem_append] at member
    cases member with
    | inl h => have bounds := leftSegment.2 location h; omega
    | inr h => have bounds := rightSegment.2 location h; omega

private theorem locationSegment_singleton (location : Nat) :
    locationSegment [location] location (location + 2) := by
  simp [locationSegment]

private theorem locationSegment_range (start count : Nat) :
    locationSegment ((List.range count).map (fun i => start + 2 * i)) start (start + 2 * count) := by
  constructor
  · apply List.Nodup.map (fun _ _ equal => by omega) List.nodup_range
  · intro location member
    obtain ⟨index, bound, rfl⟩ := List.mem_map.mp member
    have indexBound := List.mem_range.mp bound
    omega

mutual

private theorem renumber_segment (expression : Exp) (start : Nat) :
    locationSegment (codeLocationsExp (renumber start expression).2) start (renumber start expression).1 := by
  cases expression with
  | var trace n => simp [renumber, codeLocationsExp, locationSegment]
  | ifThenElse trace condition yes no =>
    simp only [renumber, codeLocationsExp]
    apply locationSegment_append
      (locationSegment_append (renumber_segment condition start)
        (renumber_segment yes (renumber start condition).1)
        (renumber_start_le condition start) (renumber_start_le yes (renumber start condition).1))
      (renumber_segment no (renumber (renumber start condition).1 yes).1)
      (by have a := renumber_start_le condition start; have b := renumber_start_le yes (renumber start condition).1; omega)
      (renumber_start_le no (renumber (renumber start condition).1 yes).1)
  | «let» trace bindings body =>
    simpa only [renumber, codeLocationsExp] using
      locationSegment_append (renumberList_segment bindings start)
        (renumber_segment body (renumberList start bindings).1)
        (renumberList_start_le bindings start) (renumber_start_le body (renumberList start bindings).1)
  | raise trace body | tick trace body =>
    simpa [renumber, codeLocationsExp] using renumber_segment body start
  | handle trace body handler =>
    simpa only [renumber, codeLocationsExp] using
      locationSegment_append (renumber_segment body start) (renumber_segment handler (renumber start body).1)
        (renumber_start_le body start) (renumber_start_le handler (renumber start body).1)
  | call trace ticks dest args | op trace _ args =>
    simpa [renumber, codeLocationsExp] using renumberList_segment args start
  | app trace dest function args =>
    simpa only [renumber, codeLocationsExp] using
      locationSegment_append (renumber_segment function start) (renumberList_segment args (renumber start function).1)
        (renumber_start_le function start) (renumberList_start_le args (renumber start function).1)
  | fn name dest vars arity body =>
    simpa only [renumber, codeLocationsExp, Option.getD_some] using
      locationSegment_append (renumber_segment body start) (locationSegment_singleton (renumber start body).1)
        (renumber_start_le body start) (Nat.le_add_right _ _)
  | letrec names dest vars functions body =>
    let middle := (renumberFuns start functions).1
    let count := (renumberFuns start functions).2.length
    have bounds : start ≤ middle + 2 * count := by
      have before := renumberFuns_start_le functions start
      dsimp [middle, count]
      omega
    have rangeLe : middle ≤ middle + 2 * count := by omega
    simpa only [renumber, codeLocationsExp, Option.getD_some] using
      locationSegment_append
        (locationSegment_append (renumberFuns_segment functions start) (locationSegment_range middle count)
          (renumberFuns_start_le functions start) rangeLe)
        (renumber_segment body (middle + 2 * count)) bounds
        (renumber_start_le body (middle + 2 * count))
termination_by sizeOf expression

private theorem renumberList_segment (expressions : List Exp) (start : Nat) :
    locationSegment (codeLocations (renumberList start expressions).2) start (renumberList start expressions).1 := by
  cases expressions with
  | nil => simp [renumberList, codeLocations, locationSegment]
  | cons first rest =>
    simpa only [renumberList, codeLocations] using
      locationSegment_append (renumber_segment first start) (renumberList_segment rest (renumber start first).1)
        (renumber_start_le first start) (renumberList_start_le rest (renumber start first).1)
termination_by sizeOf expressions

private theorem renumberFuns_segment (functions : List (Nat × Exp)) (start : Nat) :
    locationSegment (codeLocationsFuns (renumberFuns start functions).2) start (renumberFuns start functions).1 := by
  cases functions with
  | nil => simp [renumberFuns, codeLocationsFuns, locationSegment]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simpa only [renumberFuns, codeLocationsFuns] using
        locationSegment_append (renumber_segment body start) (renumberFuns_segment rest (renumber start body).1)
          (renumber_start_le body start) (renumberFuns_start_le rest (renumber start body).1)
termination_by sizeOf functions
decreasing_by all_goals (subst_vars; simp_wf; omega)

end

/-- Numbering assigns distinct locations to closures in every expression list. -/
theorem renumberList_codeLocations_nodup (expressions : List Exp) (start : Nat) :
    (codeLocations (renumberList start expressions).2).Nodup :=
  (renumberList_segment expressions start).1

/-- Incremental numbering also produces distinct closure locations; its
leading entry marker has no closure locations. -/
theorem compileInc_codeLocations_nodup (start : Nat) (expressions : List Exp) :
    (codeLocations (compileInc start expressions).2).Nodup := by
  have distinct := renumberList_codeLocations_nodup expressions
    (let next := start + max expressions.length 1; if next % 2 = 0 then next else next + 1)
  simpa [compileInc, codeLocations, codeLocationsExp] using distinct

end Flapjack.Compiler.Backend.ClosNumber
