module

public import Flapjack.Compiler.Backend.PatternSemantics

@[expose] public section

/-! Pattern-exhaustiveness matrix transformations. The total recursive
decision procedure is defined in the `Exhaustive` module. -/
namespace Flapjack.Compiler.Backend.PatternExh
open PatternSemantics

/-- A constructor class, retaining both tag and arity. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "ctor"]
inductive Ctor where
  | tagC : Nat → Nat → Ctor
  | tupC : Nat → Ctor
  | refC
  deriving DecidableEq, Repr

/-- Arity of a constructor class. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "ctor_arity_def"]
def ctorArity : Ctor → Nat
  | .tagC _ a | .tupC a => a
  | .refC => 1

/-- A list of unconditional patterns of the requested length. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "anys_def"]
def anys : Nat → List Pat
  | 0 => []
  | n + 1 => .any :: anys n

/-- Prefix every row with the given value. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "add_head_def"]
def addHead {α : Type} (x : α) : List (List α) → List (List α)
  | [] => []
  | ys :: yss => (x :: ys) :: addHead x yss

/-- Ordered Cartesian product of a column and existing rows. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mk_prods_def"]
def mkProds {α : Type} : List α → List (List α) → List (List α)
  | [], _ => []
  | x :: xs, ys => addHead x ys ++ mkProds xs ys

/-- Wrap all patterns in a reference pattern. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mk_refs_def"]
def mkRefs : List Pat → List Pat
  | [] => []
  | p :: ps => .ref p :: mkRefs ps

/-- Wrap each pattern row in the same constructor pattern. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mk_conses_def"]
def mkConses (t : Option (Nat × Option (List (Nat × Nat)))) : List (List Pat) → List Pat
  | [] => []
  | ps :: pss => .cons t ps :: mkConses t pss

mutual
/-- Expand alternatives into an ordered list of alternative-free patterns. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "expand_def"]
def expand : Pat → List Pat
  | .any => [.any]
  | .lit l => [.lit l]
  | .or p q => expand p ++ expand q
  | .ref p => mkRefs (expand p)
  | .cons t ps => mkConses t (expandList ps)

/-- Ordered product expansion for constructor argument patterns. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "expand_def"]
def expandList : List Pat → List (List Pat)
  | [] => [[]]
  | p :: ps => mkProds (expand p) (expandList ps)
end

/-- Turn each element into a one-column matrix row. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "mk_rows_def"]
def mkRows {α : Type} : List α → List (List α)
  | [] => []
  | p :: ps => [p] :: mkRows ps

/-- Expand alternative patterns into a matrix, discarding row payloads. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "or_rows_def"]
def orRows {α : Type} : List (Pat × α) → List (List Pat)
  | [] => []
  | (p, _) :: rows => mkRows (expand p) ++ orRows rows

/-- Convert sibling tag/arity pairs into constructor classes. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "tag_ctors_def"]
def tagCtors : List (Nat × Nat) → List Ctor
  | [] => []
  | (t, a) :: xs => .tagC t a :: tagCtors xs

/-- Remove duplicates while preserving each constructor's last occurrence.
The executable specializes the source's polymorphic operation to `Ctor`. -/
def ctorNub : List Ctor → List Ctor
  | [] => []
  | x :: xs => if x ∈ xs then ctorNub xs else x :: ctorNub xs

/-- Obtain the constructor information available from a pattern. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "ctors_of_def"]
def ctorsOf : Pat → Option (List Ctor)
  | .any | .lit _ | .or _ _ => none
  | .ref _ => some [.refC]
  | .cons none qs => some [.tupC qs.length]
  | .cons (some (_, none)) _ => none
  | .cons (some (t, some siblings)) qs => some (ctorNub (.tagC t qs.length :: tagCtors siblings))

/-- Keep members of the first constructor list that occur in the second.
The executable specializes the source's polymorphic operation to `Ctor`. -/
def ctorKeep : List Ctor → List Ctor → List Ctor
  | [], _ => []
  | x :: xs, ys => if x ∈ ys then x :: ctorKeep xs ys else ctorKeep xs ys

/-- Intersect known constructor classes, treating unknown as no restriction.
The executable specializes the source's polymorphic operation to `Ctor`. -/
def ctorInter : Option (List Ctor) → Option (List Ctor) → Option (List Ctor)
  | none, ys => ys
  | xs, none => xs
  | some xs, some ys => some (ctorKeep xs ys)

section SourcePolymorphic
open Classical

/-- HOL's unrestricted polymorphic duplicate elimination. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "ctor_nub_def"]
noncomputable def ctorNubHOL {α : Type} : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then ctorNubHOL xs else x :: ctorNubHOL xs

/-- HOL's unrestricted polymorphic membership filter. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "ctor_keep_def"]
noncomputable def ctorKeepHOL {α : Type} : List α → List α → List α
  | [], _ => []
  | x :: xs, ys => if x ∈ ys then x :: ctorKeepHOL xs ys else ctorKeepHOL xs ys

/-- HOL's unrestricted optional-list intersection. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "ctor_inter_def"]
noncomputable def ctorInterHOL {α : Type} : Option (List α) → Option (List α) → Option (List α)
  | none, ys => ys
  | xs, none => xs
  | some xs, some ys => some (ctorKeepHOL xs ys)

/-- The executed constructor-specific duplicate elimination agrees with the
source operation at the constructor carrier. -/
theorem ctorNub_eq_HOL (xs : List Ctor) : ctorNub xs = ctorNubHOL xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ctorNub, ctorNubHOL, ih]

/-- The executed constructor filter agrees with the source specialization. -/
theorem ctorKeep_eq_HOL (xs ys : List Ctor) : ctorKeep xs ys = ctorKeepHOL xs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ctorKeep, ctorKeepHOL, ih]

/-- The executed constructor intersection agrees with the source specialization. -/
theorem ctorInter_eq_HOL (xs ys : Option (List Ctor)) : ctorInter xs ys = ctorInterHOL xs ys := by
  cases xs <;> cases ys <;> simp [ctorInter, ctorInterHOL, ctorKeep_eq_HOL]
end SourcePolymorphic

/-- Combine the constructor information in a matrix's first column. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "col_ctors_def"]
def colCtors : List (List Pat) → Option (List Ctor)
  | [] => none
  | [] :: rows => colCtors rows
  | (p :: _) :: rows => ctorInter (ctorsOf p) (colCtors rows)

/-- Specialize a row for a constructor, preserving the argument order. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "spec_row_def"]
def specRow (c : Ctor) : List Pat → List (List Pat)
  | [] => []
  | .any :: rest => [anys (ctorArity c) ++ rest]
  | .cons none qs :: rest => if c = .tupC qs.length then [qs ++ rest] else []
  | .cons (some (tag, _)) qs :: rest => if c = .tagC tag qs.length then [qs ++ rest] else []
  | .ref q :: rest => if c = .refC then [q :: rest] else []
  | .lit _ :: _ | .or _ _ :: _ => []

/-- Specialize every row for one constructor. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "spec_mat_def"]
def specMat (c : Ctor) : List (List Pat) → List (List Pat)
  | [] => []
  | r :: rows => specRow c r ++ specMat c rows

/-- Build a specialized matrix for each possible constructor. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "spec_mats_def"]
def specMats : List Ctor → List (List Pat) → List (List (List Pat))
  | [], _ => []
  | c :: cs, rows => specMat c rows :: specMats cs rows

/-- Remove a wildcard head, rejecting other row heads. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "default_row_def"]
def defaultRow : List Pat → List (List Pat)
  | .any :: rest => [rest]
  | _ => []

/-- Form the wildcard default matrix in the source order. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "default_mat_def"]
def defaultMat : List (List Pat) → List (List Pat)
  | [] => []
  | r :: rows => defaultRow r ++ defaultMat rows

end Flapjack.Compiler.Backend.PatternExh
