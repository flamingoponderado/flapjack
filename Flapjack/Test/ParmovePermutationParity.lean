import Flapjack.Compiler.Backend.Parmove.Permutation
namespace Flapjack.Test.ParmovePermutationParity
open Flapjack.Compiler.Backend.Parmove
private def env (r : Nat) := r + 10
#guard parsem [(1,2),(3,1),(4,2)] env 1 = 12
#guard parsem [(4,2),(3,1),(1,2)] env 1 = 12
#guard parsem [(1,2),(3,1),(4,2)] env 3 = 11
#guard parsem [(4,2),(3,1),(1,2)] env 3 = 11
#guard parsem [(1,2),(3,1),(4,2)] env 4 = 12
#guard parsem [(4,2),(3,1),(1,2)] env 4 = 12
#guard parsem [(1,2),(1,3)] env 1 = 13
#guard parsem [(1,3),(1,2)] env 1 = 12
#guard parsem [(1,2),(2,1)] env 2 = 11
#guard parsem [] env 7 = 17
example : parsem (β := Nat) [(1,2),(3,1),(4,2)] =
    parsem [(4,2),(3,1),(1,2)] := by
  apply parsem_perm
  constructor
  · simp [windmill]
  · exact (List.reverse_perm _).symm
example {α β : Type} [DecidableEq α] (first second : List (α × α))
    (h : windmill first ∧ first.Perm second) :
    parsem (β := β) first = parsem second := parsem_perm first second h
end Flapjack.Test.ParmovePermutationParity
