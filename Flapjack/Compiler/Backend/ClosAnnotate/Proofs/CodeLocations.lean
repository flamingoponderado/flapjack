import Flapjack.Compiler.Backend.ClosAnnotate.Shift
import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

/-! Effects of closure annotation on code locations. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang ClosProps

/-- Variable shifting preserves the length of a recursive function group. -/
theorem shiftFuns_length (functions : List (Nat × Exp)) (count k : Nat) (index : Spt Nat) :
    (shiftFuns count k index functions).length = functions.length := by
  induction functions with
  | nil => simp [shiftFuns]
  | cons first rest ih => cases first; simp [shiftFuns, ih]

mutual

/-- Reindexing variables leaves the code locations of an expression unchanged. -/
theorem shiftSing_codeLocations (expression : Exp) (m l : Nat) (index : Spt Nat) :
    codeLocationsExp (shiftSing expression m l index) = codeLocationsExp expression := by
  cases expression with
  | var trace n => simp [shiftSing, codeLocationsExp]
  | ifThenElse trace condition yes no =>
    simp [shiftSing, codeLocationsExp, shiftSing_codeLocations condition, shiftSing_codeLocations yes,
      shiftSing_codeLocations no]
  | «let» trace bindings body =>
    simp [shiftSing, codeLocationsExp, shiftList_codeLocations bindings, shiftSing_codeLocations body]
  | raise trace body => simp [shiftSing, codeLocationsExp, shiftSing_codeLocations body]
  | handle trace body handler =>
    simp [shiftSing, codeLocationsExp, shiftSing_codeLocations body, shiftSing_codeLocations handler]
  | tick trace body => simp [shiftSing, codeLocationsExp, shiftSing_codeLocations body]
  | call trace ticks dest args => simp [shiftSing, codeLocationsExp, shiftList_codeLocations args]
  | app trace dest function args =>
    simp [shiftSing, codeLocationsExp, shiftSing_codeLocations function, shiftList_codeLocations args]
  | fn name dest vars arity body => simp [shiftSing, codeLocationsExp, shiftSing_codeLocations body]
  | letrec names dest vars functions body =>
    simp [shiftSing, codeLocationsExp, shiftFuns_length, shiftFuns_codeLocations functions,
      shiftSing_codeLocations body]
  | op trace op args => simp [shiftSing, codeLocationsExp, shiftList_codeLocations args]
termination_by sizeOf expression

/-- Reindexing variables preserves the code locations of an expression list. -/
theorem shiftList_codeLocations (expressions : List Exp) (m l : Nat) (index : Spt Nat) :
    codeLocations (shiftList expressions m l index) = codeLocations expressions := by
  cases expressions with
  | nil => simp [shiftList, codeLocations]
  | cons first rest =>
    simp [shiftList, codeLocations, shiftSing_codeLocations first, shiftList_codeLocations rest]
termination_by sizeOf expressions

/-- Reindexing recursive function bodies preserves their code locations. -/
theorem shiftFuns_codeLocations (functions : List (Nat × Exp)) (count k : Nat) (index : Spt Nat) :
    codeLocationsFuns (shiftFuns count k index functions) = codeLocationsFuns functions := by
  cases functions with
  | nil => simp [shiftFuns, codeLocationsFuns]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp [shiftFuns, codeLocationsFuns, shiftSing_codeLocations body, shiftFuns_codeLocations rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

/-- Free-variable discovery preserves the size of a recursive group. -/
theorem altFreeFuns_length (functions : List (Nat × Exp)) (count : Nat) :
    (altFreeFuns count functions).length = functions.length := by
  induction functions with
  | nil => simp [altFreeFuns]
  | cons first rest ih => cases first; simp [altFreeFuns, ih]

/-- Replicated zero expressions carry no closure locations. -/
theorem codeLocations_replicate_const0 (count : Nat) (trace : BackendCommon.Tra) :
    codeLocations (List.replicate count (const0 trace)) = [] := by
  induction count with
  | zero => simp [codeLocations]
  | succ count ih =>
    simp only [List.replicate_succ, codeLocations]
    rw [show codeLocationsExp (const0 trace) = [] by rfl, List.nil_append, ih]

mutual

/-- Free-variable discovery never introduces a new closure location. -/
theorem altFreeSing_codeLocations (expression : Exp) :
    codeLocationsExp (altFreeSing expression).1 ⊆ codeLocationsExp expression := by
  intro location member
  cases expression with
  | var trace n => simp [altFreeSing, codeLocationsExp] at member
  | ifThenElse trace condition yes no =>
    simp only [altFreeSing, codeLocationsExp, List.mem_append] at member ⊢
    rcases member with (h | h) | h
    · exact Or.inl (Or.inl (altFreeSing_codeLocations condition h))
    · exact Or.inl (Or.inr (altFreeSing_codeLocations yes h))
    · exact Or.inr (altFreeSing_codeLocations no h)
  | «let» trace bindings body =>
    simp only [altFreeSing] at member
    split at member
    · simp only [codeLocationsExp, codeLocations_replicate_const0, List.nil_append] at member
      simp only [codeLocationsExp, List.mem_append]
      exact Or.inr (altFreeSing_codeLocations body member)
    · simp only [codeLocationsExp, List.mem_append] at member ⊢
      cases member with
      | inl h => exact Or.inl (altFreeList_codeLocations bindings h)
      | inr h => exact Or.inr (altFreeSing_codeLocations body h)
  | raise trace body => simpa [altFreeSing, codeLocationsExp] using altFreeSing_codeLocations body (by simpa [altFreeSing, codeLocationsExp] using member)
  | tick trace body => simpa [altFreeSing, codeLocationsExp] using altFreeSing_codeLocations body (by simpa [altFreeSing, codeLocationsExp] using member)
  | handle trace body handler =>
    simp only [altFreeSing, codeLocationsExp, List.mem_append] at member ⊢
    cases member with
    | inl h => exact Or.inl (altFreeSing_codeLocations body h)
    | inr h => exact Or.inr (altFreeSing_codeLocations handler h)
  | call trace ticks dest args => simpa [altFreeSing, codeLocationsExp] using altFreeList_codeLocations args (by simpa [altFreeSing, codeLocationsExp] using member)
  | op trace op args => simpa [altFreeSing, codeLocationsExp] using altFreeList_codeLocations args (by simpa [altFreeSing, codeLocationsExp] using member)
  | app trace dest function args =>
    simp only [altFreeSing, codeLocationsExp, List.mem_append] at member ⊢
    cases member with
    | inl h => exact Or.inl (altFreeSing_codeLocations function h)
    | inr h => exact Or.inr (altFreeList_codeLocations args h)
  | fn name dest vars arity body =>
    simp only [altFreeSing, codeLocationsExp, List.mem_append, List.mem_singleton] at member ⊢
    cases member with
    | inl h => exact Or.inl (altFreeSing_codeLocations body h)
    | inr h => exact Or.inr h
  | letrec names dest vars functions body =>
    simp only [altFreeSing, codeLocationsExp, List.mem_append, List.length_map, altFreeFuns_length] at member ⊢
    rcases member with (h | h) | h
    · exact Or.inl (Or.inl (altFreeFuns_codeLocations functions functions.length h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (altFreeSing_codeLocations body h)
termination_by sizeOf expression

/-- The same containment for expression lists. -/
theorem altFreeList_codeLocations (expressions : List Exp) :
    codeLocations (altFreeList expressions).1 ⊆ codeLocations expressions := by
  intro location member
  cases expressions with
  | nil => simp [altFreeList, codeLocations] at member
  | cons first rest =>
    simp only [altFreeList, codeLocations, List.mem_append] at member ⊢
    cases member with
    | inl h => exact Or.inl (altFreeSing_codeLocations first h)
    | inr h => exact Or.inr (altFreeList_codeLocations rest h)
termination_by sizeOf expressions

/-- The same containment for the bodies of recursive groups. -/
theorem altFreeFuns_codeLocations (functions : List (Nat × Exp)) (count : Nat) :
    codeLocationsFuns ((altFreeFuns count functions).map Prod.fst) ⊆ codeLocationsFuns functions := by
  intro location member
  cases functions with
  | nil => simp [altFreeFuns, codeLocationsFuns] at member
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [altFreeFuns, List.map_cons, codeLocationsFuns, List.mem_append] at member ⊢
      cases member with
      | inl h => exact Or.inl (altFreeSing_codeLocations body h)
      | inr h => exact Or.inr (altFreeFuns_codeLocations rest count h)
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

/-- Annotation can erase unused code but introduces no closure location. -/
theorem annotateList_codeLocations (arity : Nat) (expressions : List Exp) :
    codeLocations (annotateList arity expressions) ⊆ codeLocations expressions := by
  simpa [annotateList, shiftList_codeLocations] using altFreeList_codeLocations expressions

/-- Annotation of a single expression introduces no closure location. -/
theorem annotateSing_codeLocations (arity : Nat) (expression : Exp) :
    codeLocationsExp (annotateSing arity expression) ⊆ codeLocationsExp expression := by
  simpa [annotateSing, shiftSing_codeLocations] using altFreeSing_codeLocations expression

/-- Annotating labeled functions introduces no location in their bodies. -/
theorem compile_codeLocations (program : List (Nat × Nat × Exp)) :
    codeLocations ((compile program).map (fun (_, _, body) => body)) ⊆
      codeLocations (program.map (fun (_, _, body) => body)) := by
  intro location member
  induction program with
  | nil => simp [compile, codeLocations] at member
  | cons first rest ih =>
    obtain ⟨name, arity, body⟩ := first
    simp only [compile, List.map_cons, codeLocations, List.mem_append] at member ⊢
    cases member with
    | inl h => exact Or.inl (annotateSing_codeLocations arity body h)
    | inr h => exact Or.inr (ih h)

end Flapjack.Compiler.Backend.ClosAnnotate
