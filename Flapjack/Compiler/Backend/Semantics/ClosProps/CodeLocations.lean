module

public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Flapjack.HolRef
public import Mathlib.Data.Set.Lattice

@[expose] public section

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
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "code_locs_append"]
theorem codeLocations_append (left right : List Exp) :
    codeLocations (left ++ right) = codeLocations left ++ codeLocations right := by
  induction left with
  | nil => simp [codeLocations]
  | cons first rest ih => simp [codeLocations, ih, List.append_assoc]

/-- The traversal of a cons cell is the singleton traversal followed by the tail. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "code_locs_cons"]
theorem codeLocations_cons (x : Exp) (xs : List Exp) :
    codeLocations (x :: xs) = codeLocations [x] ++ codeLocations xs := by
  simp [codeLocations]

/-- Traversing a mapped expression list flattens the per-element traversals. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "code_locs_map"]
theorem codeLocations_map {α : Type} (xs : List α) (f : α → Exp) :
    codeLocations (xs.map f) = (xs.map (fun x => codeLocations [f x])).flatten := by
  induction xs with
  | nil => simp [codeLocations]
  | cons x xs ih => simp [codeLocations, ih]

/-- The union of the per-element traversals of the second components of the
second components equals the traversal of the mapped list. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "BIGUNION_MAP_code_locs_SND_SND"]
theorem bigunion_map_codeLocations_snd_snd {α β : Type} (xs : List (α × β × Exp)) :
    ⋃₀ {s | s ∈ xs.map ((fun l => {n | n ∈ l}) ∘ codeLocations ∘
        (fun x => [Prod.snd (Prod.snd x)]))} =
      {n | n ∈ codeLocations (xs.map (Prod.snd ∘ Prod.snd))} := by
  induction xs with
  | nil => simp [codeLocations]
  | cons x xs ih =>
    have split :
        ⋃₀ {s | s ∈ ((fun l => {n | n ∈ l}) ∘ codeLocations ∘
              (fun x => [Prod.snd (Prod.snd x)])) x ::
            xs.map ((fun l => {n | n ∈ l}) ∘ codeLocations ∘
              (fun x => [Prod.snd (Prod.snd x)]))} =
          ((fun l => {n | n ∈ l}) ∘ codeLocations ∘
            (fun x => [Prod.snd (Prod.snd x)])) x ∪
          ⋃₀ {s | s ∈ xs.map ((fun l => {n | n ∈ l}) ∘ codeLocations ∘
            (fun x => [Prod.snd (Prod.snd x)]))} := by
      ext n
      simp only [Set.mem_sUnion, Set.mem_union, List.mem_cons]
      aesop
    rw [List.map_cons, split, ih]
    ext n
    simp [codeLocations]

end Flapjack.Compiler.Backend.ClosProps
