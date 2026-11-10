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

/-- Flapjack's mutual-recursion helper for traversing recursive function
bodies; HOL expresses this using `MAP SND` and the list traversal. -/
def getSrcNamesFuns : List (Nat × Exp) → Spt MlString → Spt MlString
  | [], table => table
  | (_, x) :: xs, table => getSrcNamesFuns xs (getSrcNamesSing x table)
end

private theorem sizeOf_map_snd_le (xs : List (Nat × Exp)) :
    sizeOf (xs.map Prod.snd) ≤ sizeOf xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases x; simp_wf; omega

/-- Collect source names using the original list-shaped traversal. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "get_src_names_def"]
def getSrcNames : List Exp → Spt MlString → Spt MlString
  | [], table => table
  | x :: y :: xs, table => getSrcNames (y :: xs) (getSrcNames [x] table)
  | [.ifThenElse _ x y z], table => getSrcNames [x] (getSrcNames [y] (getSrcNames [z] table))
  | [.var _ _], table => table
  | [.let _ xs x], table => getSrcNames (x :: xs) table
  | [.raise _ x], table | [.tick _ x], table => getSrcNames [x] table
  | [.handle _ x y], table => getSrcNames [x] (getSrcNames [y] table)
  | [.call _ _ _ xs], table | [.op _ _ xs], table => getSrcNames xs table
  | [.app _ _ x xs], table => getSrcNames (x :: xs) table
  | [.fn name loc _ _ x], table =>
      let table := getSrcNames [x] table
      match loc with | none => table | some n => addSrcNames n [name] table
  | [.letrec names loc _ funs x], table =>
      let table := getSrcNames (funs.map Prod.snd) table
      let table := getSrcNames [x] table
      match loc with | none => table | some n => addSrcNames n names table
termination_by es _ => sizeOf es
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals try (cases y <;> simp_wf <;> omega)
  all_goals simp only [List.map_attach_eq_pmap, List.pmap_eq_map] at *
  all_goals have bound := sizeOf_map_snd_le funs
  all_goals omega

/-- The recursive-group clause expressed with HOL's ordinary `MAP SND`.
This Flapjack-specific equation removes termination evidence from the recursion. -/
theorem getSrcNames_letrec (names : List MlString) (loc : Option Nat) (vars : Option (List Nat))
    (funs : List (Nat × Exp)) (body : Exp) (table : Spt MlString) :
    getSrcNames [.letrec names loc vars funs body] table =
      let table := getSrcNames (funs.map Prod.snd) table
      let table := getSrcNames [body] table
      match loc with | none => table | some n => addSrcNames n names table := by
  cases loc <;> simp [getSrcNames]

/-- The factored recursive-group traversal agrees with the list traversal.
This Flapjack-specific helper has no separate HOL declaration. -/
theorem getSrcNamesFuns_eq (funs : List (Nat × Exp)) (table : Spt MlString) :
    getSrcNamesFuns funs table = getSrcNamesList (funs.map Prod.snd) table := by
  induction funs generalizing table with
  | nil => rfl
  | cons entry rest ih =>
    cases entry
    simp [getSrcNamesFuns, getSrcNamesList, ih]

/-- The original and singleton/list name traversals agree. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "get_src_names_sing_eq"]
theorem getSrcNames_sing_eq :
    (∀ e table, getSrcNames [e] table = getSrcNamesSing e table) ∧
    (∀ es table, getSrcNames es table = getSrcNamesList es table) := by
  have all (es : List Exp) (table : Spt MlString) :
      getSrcNames es table = getSrcNamesList es table := by
    fun_induction getSrcNames es table <;> (try dsimp only at *) <;>
      simp_all (config := { zetaDelta := true }) [getSrcNamesList, getSrcNamesSing, getSrcNamesFuns_eq,
        List.map_attach_eq_pmap, List.pmap_eq_map]
  exact ⟨fun e table => by simpa [getSrcNamesList] using all [e] table, all⟩

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
