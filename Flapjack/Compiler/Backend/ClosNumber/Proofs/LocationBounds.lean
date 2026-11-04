import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants

/-! Bounds on code locations produced by closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

mutual

/-- Every closure location produced by numbering an expression lies between
the input and output numbering states. -/
theorem renumber_location_bounds (expression : Exp) (start location : Nat)
    (member : location ∈ codeLocationsExp (renumber start expression).2) :
    start ≤ location ∧ location < (renumber start expression).1 := by
  cases expression with
  | var trace n => simp [renumber, codeLocationsExp] at member
  | ifThenElse trace condition yes no =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    rcases member with (h | h) | h
    · have b := renumber_location_bounds condition start location h
      have m1 := renumber_start_le yes (renumber start condition).1
      have m2 := renumber_start_le no (renumber (renumber start condition).1 yes).1
      simp only [renumber]
      omega
    · have b := renumber_location_bounds yes (renumber start condition).1 location h
      have m1 := renumber_start_le condition start
      have m2 := renumber_start_le no (renumber (renumber start condition).1 yes).1
      simp only [renumber]
      omega
    · have b := renumber_location_bounds no (renumber (renumber start condition).1 yes).1 location h
      have m1 := renumber_start_le condition start
      have m2 := renumber_start_le yes (renumber start condition).1
      simp only [renumber]
      omega
  | «let» trace bindings body =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    cases member with
    | inl h =>
      have b := renumberList_location_bounds bindings start location h
      have m := renumber_start_le body (renumberList start bindings).1
      simp only [renumber]
      omega
    | inr h =>
      have b := renumber_location_bounds body (renumberList start bindings).1 location h
      have m := renumberList_start_le bindings start
      simp only [renumber]
      omega
  | raise trace body => simpa [renumber, codeLocationsExp] using renumber_location_bounds body start location (by simpa [renumber, codeLocationsExp] using member)
  | tick trace body => simpa [renumber, codeLocationsExp] using renumber_location_bounds body start location (by simpa [renumber, codeLocationsExp] using member)
  | handle trace body handler =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    cases member with
    | inl h =>
      have b := renumber_location_bounds body start location h
      have m := renumber_start_le handler (renumber start body).1
      simp only [renumber]
      omega
    | inr h =>
      have b := renumber_location_bounds handler (renumber start body).1 location h
      have m := renumber_start_le body start
      simp only [renumber]
      omega
  | call trace ticks dest args => simpa [renumber, codeLocationsExp] using renumberList_location_bounds args start location (by simpa [renumber, codeLocationsExp] using member)
  | op trace op args => simpa [renumber, codeLocationsExp] using renumberList_location_bounds args start location (by simpa [renumber, codeLocationsExp] using member)
  | app trace dest function args =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    cases member with
    | inl h =>
      have b := renumber_location_bounds function start location h
      have m := renumberList_start_le args (renumber start function).1
      simp only [renumber]
      omega
    | inr h =>
      have b := renumberList_location_bounds args (renumber start function).1 location h
      have m := renumber_start_le function start
      simp only [renumber]
      omega
  | fn name dest vars arity body =>
    simp only [renumber, codeLocationsExp, List.mem_append, List.mem_singleton, Option.getD_some] at member
    cases member with
    | inl h =>
      have b := renumber_location_bounds body start location h
      simp only [renumber]
      omega
    | inr h =>
      have m := renumber_start_le body start
      simp only [renumber]
      omega
  | letrec names dest vars functions body =>
    simp only [renumber, codeLocationsExp, List.mem_append, List.mem_map, List.mem_range, Option.getD_some] at member
    rcases member with (h | ⟨index, indexBound, rfl⟩) | h
    · have b := renumberFuns_location_bounds functions start location h
      have m := renumber_start_le body ((renumberFuns start functions).1 + 2 * (renumberFuns start functions).2.length)
      simp only [renumber]
      omega
    · have m := renumberFuns_start_le functions start
      have n := renumber_start_le body ((renumberFuns start functions).1 + 2 * (renumberFuns start functions).2.length)
      simp only [renumber]
      omega
    · have b := renumber_location_bounds body ((renumberFuns start functions).1 + 2 * (renumberFuns start functions).2.length) location h
      have m := renumberFuns_start_le functions start
      simp only [renumber]
      omega
termination_by sizeOf expression

/-- The interval invariant for expression lists. -/
theorem renumberList_location_bounds (expressions : List Exp) (start location : Nat)
    (member : location ∈ codeLocations (renumberList start expressions).2) :
    start ≤ location ∧ location < (renumberList start expressions).1 := by
  cases expressions with
  | nil => simp [renumberList, codeLocations] at member
  | cons first rest =>
    simp only [renumberList, codeLocations, List.mem_append] at member
    cases member with
    | inl h =>
      have b := renumber_location_bounds first start location h
      have m := renumberList_start_le rest (renumber start first).1
      simp only [renumberList]
      omega
    | inr h =>
      have b := renumberList_location_bounds rest (renumber start first).1 location h
      have m := renumber_start_le first start
      simp only [renumberList]
      omega
termination_by sizeOf expressions

/-- The interval invariant for recursive function bodies. -/
theorem renumberFuns_location_bounds (functions : List (Nat × Exp)) (start location : Nat)
    (member : location ∈ codeLocationsFuns (renumberFuns start functions).2) :
    start ≤ location ∧ location < (renumberFuns start functions).1 := by
  cases functions with
  | nil => simp [renumberFuns, codeLocationsFuns] at member
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [renumberFuns, codeLocationsFuns, List.mem_append] at member
      cases member with
      | inl h =>
        have b := renumber_location_bounds body start location h
        have m := renumberFuns_start_le rest (renumber start body).1
        simp only [renumberFuns]
        omega
      | inr h =>
        have b := renumberFuns_location_bounds rest (renumber start body).1 location h
        have m := renumber_start_le body start
        simp only [renumberFuns]
        omega
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

/-- Incremental numbering puts all main-expression closure locations within
the interval from the input state to the returned state. -/
theorem compileInc_location_bounds (start location : Nat) (expressions : List Exp)
    (member : location ∈ codeLocations (compileInc start expressions).2) :
    start ≤ location ∧ location < (compileInc start expressions).1 := by
  let next := start + max expressions.length 1
  let aligned := if next % 2 = 0 then next else next + 1
  have startBound : start ≤ aligned := by
    dsimp [aligned, next]
    split <;> omega
  have numbered : location ∈ codeLocations (renumberList aligned expressions).2 := by
    simpa [compileInc, codeLocations, codeLocationsExp, next, aligned] using member
  have bounds := renumberList_location_bounds expressions aligned location numbered
  have upper : (compileInc start expressions).1 = (renumberList aligned expressions).1 := by
    simp [compileInc, next, aligned]
  rw [upper]
  omega

/-- Closure locations are assigned only after the entry-label reservation. -/
theorem compileInc_location_after_entries (start location : Nat) (expressions : List Exp)
    (member : location ∈ codeLocations (compileInc start expressions).2) :
    start + max 1 expressions.length ≤ location := by
  let next := start + max expressions.length 1
  let aligned := if next % 2 = 0 then next else next + 1
  have lower : start + max 1 expressions.length ≤ aligned := by
    dsimp [aligned, next]
    split <;> omega
  have numbered : location ∈ codeLocations (renumberList aligned expressions).2 := by
    simpa [compileInc, codeLocations, codeLocationsExp, next, aligned] using member
  have bounds := renumberList_location_bounds expressions aligned location numbered
  omega

/-- Incremental numbering reserves enough entry labels for the whole input
list before allocating closure locations. -/
theorem compileInc_reservation (start : Nat) (expressions : List Exp) :
    start + max 1 expressions.length ≤ (compileInc start expressions).1 := by
  let next := start + max expressions.length 1
  let aligned := if next % 2 = 0 then next else next + 1
  have numbered := renumberList_start_le expressions aligned
  have lower : next ≤ aligned := by
    dsimp [aligned]
    split <;> omega
  change start + max 1 expressions.length ≤ (renumberList aligned expressions).1
  dsimp [next] at lower
  omega


mutual

/-- Numbering reserves the successor of every emitted closure location. -/
theorem renumber_location_successor_bounds (expression : Exp) (start location : Nat)
    (member : location ∈ codeLocationsExp (renumber start expression).2) :
    start ≤ location ∧ location + 1 < (renumber start expression).1 := by
  cases expression with
  | var trace n => simp [renumber, codeLocationsExp] at member
  | ifThenElse trace condition yes no =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    rcases member with (h | h) | h
    · have b := renumber_location_successor_bounds condition start location h
      have m1 := renumber_start_le yes (renumber start condition).1
      have m2 := renumber_start_le no (renumber (renumber start condition).1 yes).1
      simp only [renumber]
      omega
    · have b := renumber_location_successor_bounds yes (renumber start condition).1 location h
      have m1 := renumber_start_le condition start
      have m2 := renumber_start_le no (renumber (renumber start condition).1 yes).1
      simp only [renumber]
      omega
    · have b := renumber_location_successor_bounds no (renumber (renumber start condition).1 yes).1 location h
      have m1 := renumber_start_le condition start
      have m2 := renumber_start_le yes (renumber start condition).1
      simp only [renumber]
      omega
  | «let» trace bindings body =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    cases member with
    | inl h =>
      have b := renumberList_location_successor_bounds bindings start location h
      have m := renumber_start_le body (renumberList start bindings).1
      simp only [renumber]
      omega
    | inr h =>
      have b := renumber_location_successor_bounds body (renumberList start bindings).1 location h
      have m := renumberList_start_le bindings start
      simp only [renumber]
      omega
  | raise trace body => simpa [renumber, codeLocationsExp] using renumber_location_successor_bounds body start location (by simpa [renumber, codeLocationsExp] using member)
  | tick trace body => simpa [renumber, codeLocationsExp] using renumber_location_successor_bounds body start location (by simpa [renumber, codeLocationsExp] using member)
  | handle trace body handler =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    cases member with
    | inl h =>
      have b := renumber_location_successor_bounds body start location h
      have m := renumber_start_le handler (renumber start body).1
      simp only [renumber]
      omega
    | inr h =>
      have b := renumber_location_successor_bounds handler (renumber start body).1 location h
      have m := renumber_start_le body start
      simp only [renumber]
      omega
  | call trace ticks dest args => simpa [renumber, codeLocationsExp] using renumberList_location_successor_bounds args start location (by simpa [renumber, codeLocationsExp] using member)
  | op trace op args => simpa [renumber, codeLocationsExp] using renumberList_location_successor_bounds args start location (by simpa [renumber, codeLocationsExp] using member)
  | app trace dest function args =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    cases member with
    | inl h =>
      have b := renumber_location_successor_bounds function start location h
      have m := renumberList_start_le args (renumber start function).1
      simp only [renumber]
      omega
    | inr h =>
      have b := renumberList_location_successor_bounds args (renumber start function).1 location h
      have m := renumber_start_le function start
      simp only [renumber]
      omega
  | fn name dest vars arity body =>
    simp only [renumber, codeLocationsExp, List.mem_append, List.mem_singleton, Option.getD_some] at member
    cases member with
    | inl h =>
      have b := renumber_location_successor_bounds body start location h
      simp only [renumber]
      omega
    | inr h =>
      have m := renumber_start_le body start
      simp only [renumber]
      omega
  | letrec names dest vars functions body =>
    simp only [renumber, codeLocationsExp, List.mem_append, List.mem_map, List.mem_range, Option.getD_some] at member
    rcases member with (h | ⟨index, indexBound, rfl⟩) | h
    · have b := renumberFuns_location_successor_bounds functions start location h
      have m := renumber_start_le body ((renumberFuns start functions).1 + 2 * (renumberFuns start functions).2.length)
      simp only [renumber]
      omega
    · have m := renumberFuns_start_le functions start
      have n := renumber_start_le body ((renumberFuns start functions).1 + 2 * (renumberFuns start functions).2.length)
      simp only [renumber]
      omega
    · have b := renumber_location_successor_bounds body ((renumberFuns start functions).1 + 2 * (renumberFuns start functions).2.length) location h
      have m := renumberFuns_start_le functions start
      simp only [renumber]
      omega
termination_by sizeOf expression

/-- The successor-bound invariant for expression lists. -/
theorem renumberList_location_successor_bounds (expressions : List Exp) (start location : Nat)
    (member : location ∈ codeLocations (renumberList start expressions).2) :
    start ≤ location ∧ location + 1 < (renumberList start expressions).1 := by
  cases expressions with
  | nil => simp [renumberList, codeLocations] at member
  | cons first rest =>
    simp only [renumberList, codeLocations, List.mem_append] at member
    cases member with
    | inl h =>
      have b := renumber_location_successor_bounds first start location h
      have m := renumberList_start_le rest (renumber start first).1
      simp only [renumberList]
      omega
    | inr h =>
      have b := renumberList_location_successor_bounds rest (renumber start first).1 location h
      have m := renumber_start_le first start
      simp only [renumberList]
      omega
termination_by sizeOf expressions

/-- The successor-bound invariant for recursive function bodies. -/
theorem renumberFuns_location_successor_bounds (functions : List (Nat × Exp)) (start location : Nat)
    (member : location ∈ codeLocationsFuns (renumberFuns start functions).2) :
    start ≤ location ∧ location + 1 < (renumberFuns start functions).1 := by
  cases functions with
  | nil => simp [renumberFuns, codeLocationsFuns] at member
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [renumberFuns, codeLocationsFuns, List.mem_append] at member
      cases member with
      | inl h =>
        have b := renumber_location_successor_bounds body start location h
        have m := renumberFuns_start_le rest (renumber start body).1
        simp only [renumberFuns]
        omega
      | inr h =>
        have b := renumberFuns_location_successor_bounds rest (renumber start body).1 location h
        have m := renumber_start_le body start
        simp only [renumberFuns]
        omega
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end


/-- Incremental numbering reserves each closure label and its successor. -/
theorem compileInc_location_successor_bounds (start location : Nat) (expressions : List Exp)
    (member : location ∈ codeLocations (compileInc start expressions).2) :
    start ≤ location ∧ location + 1 < (compileInc start expressions).1 := by
  let next := start + max expressions.length 1
  let aligned := if next % 2 = 0 then next else next + 1
  have startBound : start ≤ aligned := by
    dsimp [aligned, next]
    split <;> omega
  have numbered : location ∈ codeLocations (renumberList aligned expressions).2 := by
    simpa [compileInc, codeLocations, codeLocationsExp, next, aligned] using member
  have bounds := renumberList_location_successor_bounds expressions aligned location numbered
  have upper : (compileInc start expressions).1 = (renumberList aligned expressions).1 := by
    simp [compileInc, next, aligned]
  rw [upper]
  omega


end Flapjack.Compiler.Backend.ClosNumber
