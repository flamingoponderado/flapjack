module

public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Flapjack.Misc.Sptree

@[expose] public section

/-! Source-name table collection for closure-converted code. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Basis.Pure.MlString ClosLang

/-- Add the closure and direct-call names at consecutive locations. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "add_src_names_def"]
def addSrcNames (n : Nat) : List MlString → Spt MlString → Spt MlString
  | [], table => table
  | x :: xs, table =>
      addSrcNames (n + 2) xs (sptInsert n (MlString.concat [x, ofString "_clos"])
        (sptInsert (n + 1) x table))

mutual
/-- Collect named functions from one closure expression in source order. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "get_src_names_sing_def"]
def getSrcNamesSing : Exp → Spt MlString → Spt MlString
  | .ifThenElse _ x y z, table => getSrcNamesSing x (getSrcNamesSing y (getSrcNamesSing z table))
  | .var _ _, table => table
  | .let _ xs x, table => getSrcNamesList xs (getSrcNamesSing x table)
  | .raise _ x, table | .tick _ x, table => getSrcNamesSing x table
  | .handle _ x y, table => getSrcNamesSing x (getSrcNamesSing y table)
  | .call _ _ _ xs, table | .op _ _ xs, table => getSrcNamesList xs table
  | .app _ _ x xs, table => getSrcNamesList xs (getSrcNamesSing x table)
  | .fn name loc _ _ x, table =>
      let table' := getSrcNamesSing x table
      match loc with | none => table' | some n => addSrcNames n [name] table'
  | .letrec names loc _ funs x, table =>
      let table0 := getSrcNamesFuns funs table
      let table1 := getSrcNamesSing x table0
      match loc with | none => table1 | some n => addSrcNames n names table1

/-- List clauses for source-name collection. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "get_src_names_sing_def"]
def getSrcNamesList : List Exp → Spt MlString → Spt MlString
  | [], table => table
  | x :: xs, table => getSrcNamesList xs (getSrcNamesSing x table)

/-- Traverse the bodies in a recursive function group. -/
def getSrcNamesFuns : List (Nat × Exp) → Spt MlString → Spt MlString
  | [], table => table
  | (_, x) :: xs, table => getSrcNamesFuns xs (getSrcNamesSing x table)
end

/-- The recursive-function bodies in source order (HOL's `MAP SND funs`). -/
def funBodies : List (Nat × Exp) → List Exp
  | [] => []
  | (_, body) :: rest => body :: funBodies rest

/-- The structural traversal is HOL's mapped body list. -/
theorem funBodies_eq_map (funs : List (Nat × Exp)) :
    funBodies funs = funs.map Prod.snd := by
  induction funs with
  | nil => simp [funBodies]
  | cons pair rest ih =>
    obtain ⟨number, body⟩ := pair
    simp [funBodies, ih]

/-- Mapping the recursive-function bodies does not increase the term size. -/
theorem sizeOf_funBodies_le (funs : List (Nat × Exp)) :
    sizeOf (funBodies funs) ≤ sizeOf funs := by
  induction funs with
  | nil => simp [funBodies]
  | cons pair rest ih =>
    obtain ⟨number, body⟩ := pair
    simp [funBodies] at ih ⊢
    omega

/-- Every expression has positive size, so a list's tail contributes at least one. -/
theorem one_le_sizeOf_exp (expression : Exp) : 1 ≤ sizeOf expression := by
  cases expression <;> simp <;> omega

/-- Collect names by list recursion: the empty list, HOL's per-constructor
singleton clauses, and the multi-element split `x :: y :: xs`. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "get_src_names_def"]
def getSrcNames : List Exp → Spt MlString → Spt MlString
  | [], table => table
  | [.ifThenElse _ x y z], table =>
      getSrcNames [x] (getSrcNames [y] (getSrcNames [z] table))
  | [.var _ _], table => table
  | [.«let» _ xs x], table => getSrcNames (x :: xs) table
  | [.raise _ x], table => getSrcNames [x] table
  | [.handle _ x y], table => getSrcNames [x] (getSrcNames [y] table)
  | [.tick _ x], table => getSrcNames [x] table
  | [.call _ _ _ xs], table => getSrcNames xs table
  | [.op _ _ xs], table => getSrcNames xs table
  | [.app _ _ x xs], table => getSrcNames (x :: xs) table
  | [.fn name loc _ _ x], table =>
      let table1 := getSrcNames [x] table
      match loc with | none => table1 | some n => addSrcNames n [name] table1
  | [.letrec names loc _ funs x], table =>
      let table0 := getSrcNames (funBodies funs) table
      let table1 := getSrcNames [x] table0
      match loc with | none => table1 | some n => addSrcNames n names table1
  | x :: y :: xs, table => getSrcNames (y :: xs) (getSrcNames [x] table)
termination_by es _ => sizeOf es
decreasing_by
  all_goals
    try have hx : 1 ≤ sizeOf x := one_le_sizeOf_exp x
    try have hy : 1 ≤ sizeOf y := one_le_sizeOf_exp y
    try have hz : 1 ≤ sizeOf z := one_le_sizeOf_exp z
    try have hf : sizeOf (funBodies funs) ≤ sizeOf funs := sizeOf_funBodies_le funs
    simp
    omega

/-- Construct the name table for stubs, top-level declarations and closures. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "make_name_alist_def"]
def makeNameAlist {α β : Type} (nums : List Nat) (prog : List (α × β × Exp))
    (nstubs decStart decLength : Nat) : Spt MlString :=
  let names := getSrcNames (prog.map (fun (_, _, e) => e)) .ln
  sptFromAList (nums.map fun n =>
    (n, if n < nstubs then
      if n = nstubs - 1 then ofString "bvl_init"
      else if n = nstubs - 2 then ofString "bvl_force"
      else ofString "bvl_stub"
    else
      let loc := n - nstubs
      if decStart ≤ loc ∧ loc < decStart + decLength then ofString "dec"
      else (sptLookup loc names).getD (ofString "unknown_clos_fun")))

end Flapjack.Compiler.Backend.ClosToBvl
