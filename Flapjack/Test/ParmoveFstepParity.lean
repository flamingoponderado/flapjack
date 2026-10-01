import Flapjack.Compiler.Backend.Parmove

namespace Flapjack.Test.ParmoveFstepParity
open Flapjack.Compiler.Backend.Parmove

/-! Direct original HOL `fstep` observations in
`scripts/hol-probes/parmove_fstep_probe.out`. The cases cover every branch,
including duplicate matching sources (first match), cycle save through `none`,
and a pre-existing emitted suffix. These are transition tests, not a proof of
the complete parallel-move semantic correctness theorem. -/

def r (n : Nat) : Option Nat := some n

#guard fstep (α := Nat) ([], [], [(r 8, r 9)]) == ([], [], [(r 8, r 9)]) -- fs_final
#guard fstep (α := Nat) ([(r 1, r 1), (r 2, r 3)], [], []) ==
  ([(r 2, r 3)], [], []) -- fs_self
#guard fstep (α := Nat) ([(r 1, r 2), (r 3, r 4)], [], []) ==
  ([(r 3, r 4)], [(r 1, r 2)], []) -- fs_start
#guard fstep (α := Nat) ([(r 7, r 8), (r 3, r 1), (r 4, r 1)], [(r 1, r 2)], []) ==
  ([(r 7, r 8), (r 4, r 1)], [(r 3, r 1), (r 1, r 2)], []) -- fs_first
#guard fstep (α := Nat) ([(r 7, r 8)], [(r 1, r 2)], [(r 8, r 9)]) ==
  ([(r 7, r 8)], [], [(r 1, r 2), (r 8, r 9)]) -- fs_single
#guard fstep (α := Nat) ([], [(r 1, r 2), (r 2, r 3), (r 3, r 4)], []) ==
  ([], [(r 2, r 3), (r 3, r 4)], [(r 1, r 2)]) -- fs_chain
#guard fstep (α := Nat) ([], [(r 1, r 2), (r 2, r 1)], []) ==
  ([], [(r 2, none)], [(r 1, r 2), (none, r 1)]) -- fs_cycle
#guard fstep (α := Nat) ([], [(r 1, r 2), (r 2, r 3), (r 3, r 1)], [(r 8, r 9)]) ==
  ([], [(r 2, r 3), (r 3, none)], [(r 1, r 2), (none, r 1), (r 8, r 9)]) -- fs_cycle_long
#guard fstep (α := Nat) ([(r 2, none)], [(none, r 1)], []) ==
  ([], [(r 2, none), (none, r 1)], []) -- fs_temp_match
#guard fstep (α := Nat) ([(none, none)], [], []) == ([], [], []) -- fs_temp_self

example (pending active emitted : List (Move Nat))
    (unfinished : pending ≠ [] ∨ active ≠ []) :
    measure (fstep (pending, active, emitted)) < measure (pending, active, emitted) :=
  fstep_decreases pending active emitted unfinished

/-! Nine complete scheduler observations from the direct original HOL
`parmove_scheduler_probe.out`, including unconstrained temporary/self input and
repeated destinations. They do not establish full `parmove_correct`. -/
#guard pmov (α := Nat) ([], [], [(r 8, r 9)]) == ([], [], [(r 8, r 9)])
#guard pmov (α := Nat) ([(none, none)], [], []) == ([], [], [])
#guard parmove ([] : List (Nat × Nat)) == []
#guard parmove [((1 : Nat), 1)] == []
#guard parmove [((1 : Nat), 2)] == [(r 1, r 2)]
#guard parmove [((1 : Nat), 2), (2, 3), (3, 4)] == [(r 1, r 2), (r 2, r 3), (r 3, r 4)]
#guard parmove [((1 : Nat), 2), (2, 1)] == [(none, r 2), (r 2, r 1), (r 1, none)]
#guard parmove [((1 : Nat), 2), (2, 3), (3, 1)] ==
  [(none, r 2), (r 2, r 3), (r 3, r 1), (r 1, none)]
#guard parmove [((1 : Nat), 2), (1, 3)] == [(r 1, r 2), (r 1, r 3)]

end Flapjack.Test.ParmoveFstepParity
