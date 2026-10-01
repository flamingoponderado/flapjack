import Flapjack.Pancake.WordLang.OccurrencesExact

/-! Fresh original WordLangTheory rows from
word_lang_occurrences_exact_probe.out. Every example invokes a newly tagged
exact occurrence predicate, with native Spt cutsets and BitVec 8 programs. -/
namespace Flapjack.Test.WordLangOccurrencesExactParity
private def even (n : Nat) : Bool := decide (n % 2 = 0)
private def cut (keys : List Nat) : WordLangNumSetHOL :=
  sptFromAList (keys.map (fun key => (key, ())))

-- name_empty=T
example : everyNameHOL even (cut [], cut []) = true := by cbv
-- name_even=T
example : everyNameHOL even (cut [2, 4], cut [6]) = true := by cbv
-- name_odd=F
example : everyNameHOL even (cut [2], cut [3]) = false := by cbv
-- var_move_even=T
example : everyVarHOL (width := 8) even (.move 0 [(2, 4)]) = true := by cbv
-- var_move_odd=F
example : everyVarHOL (width := 8) even (.move 0 [(2, 3)]) = false := by cbv
-- var_loop_live=F
example : everyVarHOL (width := 8) even (.loop (cut [3]) .skip (cut [2])) = false := by cbv
-- stack_loop_live=T
example : everyStackVarHOL (width := 8) even (.loop (cut [3]) .skip (cut [2])) = true := by cbv
-- stack_alloc_odd=F
example : everyStackVarHOL (width := 8) even (.alloc 2 (cut [], cut [3])) = false := by cbv
-- var_call_none=T: NONE return ignores the handler, including its odd name.
example : everyVarHOL (width := 8) even
    (.call none none [2] (some (3, .raise 3, 1, 0))) = true := by cbv
-- stack_call_none=T: NONE return ignores the handler cutset.
example : everyStackVarHOL (width := 8) even
    (.call none none [2] (some (3, .alloc 2 (cut [], cut [3]), 1, 0))) = true := by cbv
-- var_call_some=F: SOME return checks the handler name and body.
example : everyVarHOL (width := 8) even
    (.call (some ([2], (cut [], cut []), .skip, 1, 0)) none [2]
      (some (3, .raise 3, 1, 0))) = false := by cbv
-- stack_call_some=F: SOME return checks the handler cutset.
example : everyStackVarHOL (width := 8) even
    (.call (some ([2], (cut [], cut []), .skip, 1, 0)) none [2]
      (some (2, .alloc 2 (cut [], cut [3]), 1, 0))) = false := by cbv

def runChecks : IO Bool := do
  IO.println "PASS exact WordLang occurrence predicates match all 12 original HOL rows"
  pure true
end Flapjack.Test.WordLangOccurrencesExactParity
