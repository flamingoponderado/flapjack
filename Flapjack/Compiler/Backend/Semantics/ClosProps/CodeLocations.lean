import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.HolRef

/-! Collect closure-code locations in traversal order. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosLang

mutual

/-- Structural singleton helper for the original closure-location traversal. -/
def codeLocationsExp : Exp → List Nat
  | .var .. => []
  | .ifThenElse _ condition yes no =>
      codeLocationsExp condition ++ codeLocationsExp yes ++ codeLocationsExp no
  | .let _ bindings body => codeLocations bindings ++ codeLocationsExp body
  | .raise _ body | .tick _ body => codeLocationsExp body
  | .handle _ body handler => codeLocationsExp body ++ codeLocationsExp handler
  | .call _ _ _ args | .op _ _ args => codeLocations args
  | .app _ _ function args => codeLocationsExp function ++ codeLocations args
  | .fn _ location _ _ body => codeLocationsExp body ++ [location.getD 0]
  | .letrec _ location _ functions body =>
      codeLocationsFuns functions ++
        (List.range functions.length).map (fun i => location.getD 0 + 2 * i) ++
        codeLocationsExp body

/-- Closure locations in a list of expressions. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "code_locs_def"]
def codeLocations : List Exp → List Nat
  | [] => []
  | expression :: expressions => codeLocationsExp expression ++ codeLocations expressions

/-- Closure locations in recursive function bodies. -/
def codeLocationsFuns : List (Nat × Exp) → List Nat
  | [] => []
  | (_, body) :: functions => codeLocationsExp body ++ codeLocationsFuns functions

end

/-- The singleton traversal has the source's list form. -/
theorem codeLocations_singleton (e : Exp) : codeLocations [e] = codeLocationsExp e := by
  simp [codeLocations]

/-- The recursive-group helper traverses the bodies in source order. -/
theorem codeLocationsFuns_map (fns : List (Nat × Exp)) :
    codeLocationsFuns fns = codeLocations (fns.map Prod.snd) := by
  induction fns with
  | nil => rfl
  | cons fn fns ih =>
    obtain ⟨arity, body⟩ := fn
    simp [codeLocationsFuns, codeLocations, ih]

/-- Collecting locations distributes over expression-list concatenation. -/
theorem codeLocations_append (left right : List Exp) :
    codeLocations (left ++ right) = codeLocations left ++ codeLocations right := by
  induction left with
  | nil => simp [codeLocations]
  | cons first rest ih => simp [codeLocations, ih, List.append_assoc]

/-- A collected location occurs in the traversal of some list member. -/
theorem mem_codeLocations (location : Nat) (expressions : List Exp) :
    location ∈ codeLocations expressions ↔
      ∃ expression ∈ expressions, location ∈ codeLocationsExp expression := by
  induction expressions with
  | nil => simp [codeLocations]
  | cons first rest ih => simp [codeLocations, ih, or_and_right, exists_or]

end Flapjack.Compiler.Backend.ClosProps
