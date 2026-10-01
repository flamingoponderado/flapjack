import Flapjack.Compiler.Backend.Parmove.Semantics

namespace Flapjack.Test.ParmoveSemanticsParity
open Flapjack.Compiler.Backend.Parmove

/-! Exact rows from `parmove_semantics_probe.out`. Parallel snapshots,
sequential updated reads, repeated destinations, reverse emitted execution and
temporary-excluding equivalence are tested separately. No windmill condition
is silently assumed for the duplicate-destination observations. -/
def env (n : Nat) : Nat := n + 10

example : windmill ([(1, 2), (2, 1)] : List (Nat × Nat)) := by
  unfold windmill
  decide -- sem_windmill=T
example : ¬windmill ([(1, 2), (1, 3)] : List (Nat × Nat)) := by
  unfold windmill
  decide -- sem_repeated=F
#guard parsem [(1, 2), (2, 1)] env 1 == 12 -- sem_parallel_swap1
#guard parsem [(1, 2), (2, 1)] env 2 == 11 -- sem_parallel_swap2
#guard seqsem [(1, 2), (2, 1)] env 2 == 12 -- sem_sequential_swap2
#guard parsem [(1, 2), (1, 3)] env 1 == 13 -- sem_parallel_last
#guard seqsem [(1, 2), (1, 3)] env 1 == 13 -- sem_sequential_last
#guard parsem [(1, 2), (1, 3)] env 7 == 17 -- sem_untouched
#guard sem ([(1, 2)], [(2, 3)], [(3, 4), (4, 5)]) env 1 == 12 -- sem_state_first
#guard sem ([(1, 2)], [(2, 3)], [(3, 4), (4, 5)]) env 2 == 15 -- sem_state_second

-- sem_ignore_temp=T: equality at every real register, arbitrary temporary.
example : eqenv (fun r : Option Nat => if r.isSome then 7 else 0)
    (fun r : Option Nat => if r.isSome then 7 else 99) := by
  intro register real
  simp [real]

-- sem_real_difference=F: a real-register discrepancy is observable.
example : ¬eqenv (fun r : Option Nat => if r.isSome then 7 else 0)
    (fun r : Option Nat => if r.isSome then 8 else 0) := by
  intro equal
  have impossible := equal (some 0) rfl
  contradiction

example (first second : List (Nat × Nat)) :
    seqsem (β := Nat) (first ++ second) = seqsem second ∘ seqsem first :=
  seqsem_append first second

end Flapjack.Test.ParmoveSemanticsParity
