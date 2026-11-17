module

public import Flapjack.Compiler.Inference.Infer.Operations

@[expose] public section

/-! Duplicate detection in the inference frontend. -/
namespace Flapjack.Compiler.Inference.Infer.Duplicates
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
open Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Translator.Monadic.MonadBase

/-- Computable equality implementation used by the executable frontend. -/
def findDup {α : Type} [DecidableEq α] : List α → Option α
  | [] => none
  | x :: xs => if x ∈ xs then some x else findDup xs

/-- Computable duplicate checking with a supplied equality implementation. -/
def checkDupsExec {α state error : Type} [DecidableEq α] (l : LocErrInfo)
    (f : α → error) : List α → M state Unit (Option Flapjack.Misc.Location.Locs × error)
  | [] => ret ()
  | x :: xs => if x ∈ xs then failwith l (f x) else checkDupsExec l f xs

/-- The source operation admits every HOL equality type. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "find_dup_def"]
noncomputable def findDupHOL {α : Type} (xs : List α) : Option α :=
  @findDup α (Classical.typeDecidableEq α) xs

/-- Source duplicate checking, with unrestricted polymorphic equality. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "check_dups_def"]
noncomputable def checkDups {α state error : Type} (l : LocErrInfo)
    (f : α → error) (xs : List α) : M state Unit (Option Flapjack.Misc.Location.Locs × error) :=
  @checkDupsExec α state error (Classical.typeDecidableEq α) l f xs

/-- Executable duplicate checking agrees with unrestricted source equality. -/
theorem checkDups_eq {α state error : Type} [inst : DecidableEq α]
    (l : LocErrInfo) (f : α → error) (xs : List α) :
    checkDups (state := state) l f xs = checkDupsExec l f xs := by
  unfold checkDups
  have same : Classical.typeDecidableEq α = inst := Subsingleton.elim _ _
  rw [same]

/-- The executable equality implementation agrees with source equality. -/
theorem findDupHOL_eq {α : Type} [inst : DecidableEq α] (xs : List α) :
    findDupHOL xs = findDup xs := by
  unfold findDupHOL
  have same : Classical.typeDecidableEq α = inst := Subsingleton.elim _ _
  rw [same]

@[hol "cakeml/compiler/inference/inferScript.sml" "check_dups_eq_find_dup"]
theorem checkDupsEqFindDup {α state value error : Type}
    (l : LocErrInfo) (f : α → error) (g : M state value (Option Flapjack.Misc.Location.Locs × error))
    (xs : List α) :
    ignoreBind (checkDups l f xs) g = fun s =>
      match findDupHOL xs with
      | none => g s
      | some x => (.failure (l.loc, f x), s) := by
  classical
  unfold checkDups findDupHOL
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x ∈ xs
    · funext s
      simp [checkDupsExec, findDup, h, Operations.failwith, ignoreBind]
    · simpa [checkDupsExec, findDup, h] using ih

end Flapjack.Compiler.Inference.Infer.Duplicates
