import Flapjack.Compiler.Backend.WordAlloc.SelectRegAlloc
import Flapjack.Misc.Sptree.ToAList
namespace Flapjack.Test.WordAllocSelectRegAllocParity
open Flapjack Flapjack.RegAlloc Flapjack.WordAlloc Flapjack.Translator.Monadic.MonadBase

/-! Kernel replay of `scripts/hol-probes/word_alloc_select_reg_alloc_probe.out`:
original HOL `select_reg_alloc` runs for algorithms 0-5 (Simple, IRC with and
without spill costs, linear scan with a spill and a forced pair), each observed
through `toAList` of the returned colouring. -/

private def obs (r : Exc (Spt Nat) StateException) : Option (List (Nat × Nat)) :=
  match r with
  | .success col => some (sptToAList col)
  | .failure _ => none

private def tree1 : ClashTree := .seq (.delta [1] [5]) (.delta [9] [1, 5])

-- sra_type=:num -> num sptree$num_map option -> num -> (num # num # num) list -> clash_tree -> (num # num) list -> sptree$num_set -> (num sptree$num_map, state_exn) exc
example : Nat → Option (Spt Nat) → Nat → List (Nat × (Nat × Nat)) → ClashTree →
    List (Nat × Nat) → NumSet → Exc (Spt Nat) StateException := selectRegAlloc
-- sra_simple0=SOME [(1,0); (9,0); (5,1)]
example : obs (selectRegAlloc 0 none 2 [(1, (1, 5))] tree1 [] .ln) =
    some [(1, 0), (9, 0), (5, 1)] := by decide +kernel
-- sra_simple1=SOME [(1,0); (9,0); (5,1)]
example : obs (selectRegAlloc 1 none 2 [(1, (1, 5))] tree1 [] .ln) =
    some [(1, 0), (9, 0), (5, 1)] := by decide +kernel
-- sra_irc2=SOME [(1,0); (9,0); (5,1)]
example : obs (selectRegAlloc 2 none 2 [(1, (1, 5))] tree1 [] .ln) =
    some [(1, 0), (9, 0), (5, 1)] := by decide +kernel
-- sra_irc3_cost=SOME [(1,1); (9,2); (5,0)]
example : obs (selectRegAlloc 3 (some (sptFromAList [(1, 10), (5, 1), (9, 7)])) 1 []
    (.delta [1, 5, 9] [1, 5, 9]) [] .ln) = some [(1, 1), (9, 2), (5, 0)] := by decide +kernel
-- sra_linear4=SOME [(1,1); (9,0); (5,0)]
example : obs (selectRegAlloc 4 none 2 [(1, (1, 5))] tree1 [] .ln) =
    some [(1, 1), (9, 0), (5, 0)] := by decide +kernel
-- sra_linear5_spill=SOME [(1,0); (9,2); (5,1)]
example : obs (selectRegAlloc 5 none 1 [] (.delta [1, 5, 9] [1, 5, 9]) [] .ln) =
    some [(1, 0), (9, 2), (5, 1)] := by decide +kernel
-- sra_linear_forced=SOME [(1,0); (9,0); (5,1)]
example : obs (selectRegAlloc 4 none 2 [] (.branch (some (sptInsert 1 () .ln)) (.delta [5] [1])
    (.delta [9] [1])) [(1, 5)] .ln) = some [(1, 0), (9, 0), (5, 1)] := by decide +kernel

end Flapjack.Test.WordAllocSelectRegAllocParity
