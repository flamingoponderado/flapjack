import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationBounds

/-! Parity of the code locations allocated by closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

mutual
/-- Numbering changes the state by an even amount. -/
theorem renumber_state_parity (expression : Exp) (start : Nat) :
    (renumber start expression).1 % 2 = start % 2 := by
  cases expression with
  | var => rfl
  | ifThenElse tr x y z =>
    simp only [renumber]
    rw [renumber_state_parity z, renumber_state_parity y, renumber_state_parity x]
  | «let» tr xs x =>
    simp only [renumber]
    rw [renumber_state_parity x, renumberList_state_parity xs]
  | raise tr x | tick tr x => exact renumber_state_parity x start
  | handle tr x y =>
    simp only [renumber]
    rw [renumber_state_parity y, renumber_state_parity x]
  | call tr ticks dest xs | op tr dest xs => exact renumberList_state_parity xs start
  | app tr dest x xs =>
    simp only [renumber]
    rw [renumberList_state_parity xs, renumber_state_parity x]
  | fn name dest vars arity body =>
    simp only [renumber]
    have h := renumber_state_parity body start
    omega
  | letrec names dest vars fns body =>
    simp only [renumber]
    rw [renumber_state_parity body]
    have h := renumberFuns_state_parity fns start
    omega
termination_by sizeOf expression

/-- List numbering preserves the state parity. -/
theorem renumberList_state_parity (expressions : List Exp) (start : Nat) :
    (renumberList start expressions).1 % 2 = start % 2 := by
  cases expressions with
  | nil => rfl
  | cons first rest =>
    simp only [renumberList]
    rw [renumberList_state_parity rest, renumber_state_parity first]
termination_by sizeOf expressions

/-- Function-group numbering preserves the state parity. -/
theorem renumberFuns_state_parity (functions : List (Nat × Exp)) (start : Nat) :
    (renumberFuns start functions).1 % 2 = start % 2 := by
  cases functions with
  | nil => rfl
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [renumberFuns]
      rw [renumberFuns_state_parity rest, renumber_state_parity body]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

mutual
/-- Every location emitted by numbering has the input state's parity. -/
theorem renumber_location_parity (expression : Exp) (start location : Nat)
    (member : location ∈ codeLocationsExp (renumber start expression).2) :
    location % 2 = start % 2 := by
  cases expression with
  | var trace n => simp [renumber, codeLocationsExp] at member
  | ifThenElse trace condition yes no =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    rcases member with (h | h) | h
    · exact renumber_location_parity condition start location h
    · have p := renumber_location_parity yes (renumber start condition).1 location h
      rw [renumber_state_parity condition] at p
      exact p
    · have p := renumber_location_parity no (renumber (renumber start condition).1 yes).1 location h
      rw [renumber_state_parity yes, renumber_state_parity condition] at p
      exact p
  | «let» trace bindings body =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    cases member with
    | inl h => exact renumberList_location_parity bindings start location h
    | inr h =>
      have p := renumber_location_parity body (renumberList start bindings).1 location h
      rw [renumberList_state_parity bindings] at p
      exact p
  | raise trace body | tick trace body =>
    exact renumber_location_parity body start location (by simpa [renumber, codeLocationsExp] using member)
  | handle trace body handler =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    cases member with
    | inl h => exact renumber_location_parity body start location h
    | inr h =>
      have p := renumber_location_parity handler (renumber start body).1 location h
      rw [renumber_state_parity body] at p
      exact p
  | call trace ticks dest args | op trace dest args =>
    exact renumberList_location_parity args start location (by simpa [renumber, codeLocationsExp] using member)
  | app trace dest function args =>
    simp only [renumber, codeLocationsExp, List.mem_append] at member
    cases member with
    | inl h => exact renumber_location_parity function start location h
    | inr h =>
      have p := renumberList_location_parity args (renumber start function).1 location h
      rw [renumber_state_parity function] at p
      exact p
  | fn name dest vars arity body =>
    simp only [renumber, codeLocationsExp, List.mem_append, List.mem_singleton, Option.getD_some] at member
    cases member with
    | inl h => exact renumber_location_parity body start location h
    | inr h =>
      subst location
      exact renumber_state_parity body start
  | letrec names dest vars functions body =>
    simp only [renumber, codeLocationsExp, List.mem_append, List.mem_map, List.mem_range, Option.getD_some] at member
    rcases member with (h | ⟨index, indexBound, rfl⟩) | h
    · exact renumberFuns_location_parity functions start location h
    · have p := renumberFuns_state_parity functions start
      omega
    · have p := renumber_location_parity body ((renumberFuns start functions).1 + 2 * (renumberFuns start functions).2.length) location h
      have q := renumberFuns_state_parity functions start
      omega
termination_by sizeOf expression

/-- List numbering emits locations with the input state's parity. -/
theorem renumberList_location_parity (expressions : List Exp) (start location : Nat)
    (member : location ∈ codeLocations (renumberList start expressions).2) :
    location % 2 = start % 2 := by
  cases expressions with
  | nil => simp [renumberList, codeLocations] at member
  | cons first rest =>
    simp only [renumberList, codeLocations, List.mem_append] at member
    cases member with
    | inl h => exact renumber_location_parity first start location h
    | inr h =>
      have p := renumberList_location_parity rest (renumber start first).1 location h
      rw [renumber_state_parity first] at p
      exact p
termination_by sizeOf expressions

/-- Function-group numbering emits locations with the input state's parity. -/
theorem renumberFuns_location_parity (functions : List (Nat × Exp)) (start location : Nat)
    (member : location ∈ codeLocationsFuns (renumberFuns start functions).2) :
    location % 2 = start % 2 := by
  cases functions with
  | nil => simp [renumberFuns, codeLocationsFuns] at member
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [renumberFuns, codeLocationsFuns, List.mem_append] at member
      cases member with
      | inl h => exact renumber_location_parity body start location h
      | inr h =>
        have p := renumberFuns_location_parity rest (renumber start body).1 location h
        rw [renumber_state_parity body] at p
        exact p
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Incremental numbering allocates even closure locations. -/
theorem compileInc_location_even (start location : Nat) (expressions : List Exp)
    (member : location ∈ codeLocations (compileInc start expressions).2) :
    location % 2 = 0 := by
  let next := start + max expressions.length 1
  let aligned := if next % 2 = 0 then next else next + 1
  have even : aligned % 2 = 0 := by
    dsimp [aligned]
    split <;> omega
  have numbered : location ∈ codeLocations (renumberList aligned expressions).2 := by
    simpa [compileInc, codeLocations, codeLocationsExp, next, aligned] using member
  rw [renumberList_location_parity expressions aligned location numbered]
  exact even

end Flapjack.Compiler.Backend.ClosNumber
