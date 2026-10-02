import Flapjack.Compiler.Backend.RegAlloc.Allocator
import Flapjack.Misc.Sptree.ToAList
namespace Flapjack.Test.RegAllocAllocatorParity
open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-! Kernel replay of `scripts/hol-probes/reg_alloc_allocator_probe.out`: complete
original HOL `reg_alloc` runs (Simple and IRC, moves, spill costs, forced pairs,
physical, stack and forced-stack registers), each observed through `toAList` of
the returned colouring. -/

private def obs (r : Exc (Spt Nat) StateException) : Option (List (Nat × Nat)) :=
  match r with
  | .success col => some (sptToAList col)
  | .failure _ => none

-- ra_simple_delta=SOME [(1,0); (9,0); (5,1)]
example : obs (regAlloc .Simple none 3 [] (.delta [1, 5] [9]) [] .ln) =
    some [(1,0), (9,0), (5,1)] := by decide +kernel
-- ra_irc_move=SOME [(1,0); (9,0); (5,1)]
example : obs (regAlloc .IRC none 2 [(1, (1, 5))] (.seq (.delta [1] [5]) (.delta [9] [1, 5])) [] .ln) =
    some [(1,0), (9,0), (5,1)] := by decide +kernel
-- ra_simple_move=SOME [(1,0); (9,0); (5,1)]
example : obs (regAlloc .Simple none 2 [(1, (1, 5))] (.seq (.delta [1] [5]) (.delta [9] [1, 5])) [] .ln) =
    some [(1,0), (9,0), (5,1)] := by decide +kernel
-- ra_irc_spill_cost=SOME [(1,1); (9,2); (5,0)]
example : obs (regAlloc .IRC (some (sptFromAList [(1, 10), (5, 1), (9, 7)])) 1 [] (.delta [1, 5, 9] [1, 5, 9]) [] .ln) =
    some [(1,1), (9,2), (5,0)] := by decide +kernel
-- ra_irc_spill_deg=SOME [(1,1); (9,2); (5,0)]
example : obs (regAlloc .IRC none 1 [] (.delta [1, 5, 9] [1, 5, 9]) [] .ln) =
    some [(1,1), (9,2), (5,0)] := by decide +kernel
-- ra_simple_branch_forced=SOME [(1,0); (9,0); (5,1)]
example : obs (regAlloc .Simple none 2 [] (.branch (some (sptInsert 1 () .ln)) (.delta [5] [1]) (.delta [9] [1])) [(1, 5)] .ln) =
    some [(1,0), (9,0), (5,1)] := by decide +kernel
-- ra_irc_phys=SOME [(1,1); (5,0); (0,0); (2,1)]
example : obs (regAlloc .IRC none 3 [(5, (0, 1))] (.delta [0, 1] [2, 5]) [] .ln) =
    some [(1,1), (5,0), (0,0), (2,1)] := by decide +kernel
-- ra_irc_fs=SOME [(1,2); (5,0)]
example : obs (regAlloc .IRC none 2 [] (.delta [1, 5] []) [] (sptInsert 1 () .ln)) =
    some [(1,2), (5,0)] := by decide +kernel
-- ra_irc_stack=SOME [(7,3); (3,2); (1,0); (5,0)]
example : obs (regAlloc .IRC none 2 [] (.delta [3, 1, 7] [5]) [] .ln) =
    some [(7,3), (3,2), (1,0), (5,0)] := by decide +kernel
-- ra_irc_coalesce_chain=SOME [(1,0); (9,0); (5,0)]
example : obs (regAlloc .IRC none 2 [(3, (1, 5)), (2, (5, 9))] (.seq (.delta [1] []) (.seq (.delta [5] [1]) (.delta [9] [5]))) [] .ln) =
    some [(1,0), (9,0), (5,0)] := by decide +kernel
-- ra_irc_pressure=SOME [(1,2); (9,1); (5,0); (13,0)]
example : obs (regAlloc .IRC none 2 [(4, (1, 13))] (.seq (.delta [1, 5, 9] [13]) (.delta [13] [1, 5, 9])) [] .ln) =
    some [(1,2), (9,1), (5,0), (13,0)] := by decide +kernel
-- ra_empty=SOME []
example : obs (regAlloc .IRC none 2 [] (.set .ln) [] .ln) =
    some [] := by decide +kernel

end Flapjack.Test.RegAllocAllocatorParity
