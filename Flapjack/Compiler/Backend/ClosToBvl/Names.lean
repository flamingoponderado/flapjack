import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.Misc.Sptree

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

/-- Collect names using the singleton traversal, which HOL proves equal to
the original list-valued `get_src_names` definition. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "get_src_names_def"]
def getSrcNames (es : List Exp) (table : Spt MlString) : Spt MlString :=
  getSrcNamesList es table

/-- Construct the name table for stubs, top-level declarations and closures. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "make_name_alist_def"]
def makeNameAlist (nums : List Nat) (prog : List (Nat × Nat × Exp))
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
