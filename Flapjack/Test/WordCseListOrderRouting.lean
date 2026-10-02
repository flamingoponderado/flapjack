import Flapjack.RiscV.WordCse
import Flapjack.Compiler.Backend.WordCse.Proofs.ListOrder
open Flapjack.RiscV Flapjack.Compiler.Backend.WordCse

/-- Actual CSE fact insertion/lookup for arbitrary keys, values and initial
binding lists agrees with its former comparator. Includes replacement keys. -/
example (entries : List (List Nat × Nat)) (key query : List Nat) (value : Nat) :
  wordCseListLookup query (wordCseListInsert key value
    (entries.foldl (fun map entry => wordCseListInsert entry.1 entry.2 map)
      (∅ : WordCseFactMap))) =
  ((entries.foldl (fun (map : Std.TreeMap (List Nat) Nat) entry =>
      map.insert entry.1 entry.2) ∅).insert key value)[query]? := by
  simp only [wordCseListLookup, wordCseListInsert, WordCseFactMap]
  rw [listCmpFunctionEqStdCompare]

example : wordCseListLookup [0, 1]
    (wordCseListInsert [] 7 (wordCseListInsert [0] 8
      (wordCseListInsert [0, 1] 9 (wordCseListInsert [0, 1] 3 ∅)))) = some 9 := by decide

example : wordCseListLookup [0, 1, 0]
    (wordCseListInsert [] 7 (wordCseListInsert [0] 8
      (wordCseListInsert [0, 1] 9 ∅))) = none := by decide

example : wordCseListLookup [1208925819614629174706183]
    (wordCseListInsert [1208925819614629174706183] 5
      (wordCseListInsert [0, 0, 1] 8 ∅)) = some 5 := by decide
