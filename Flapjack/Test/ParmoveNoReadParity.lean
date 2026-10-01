import Flapjack.Compiler.Backend.Parmove.NoRead
namespace Flapjack.Test.ParmoveNoReadParity
open Flapjack.Compiler.Backend.Parmove
private def env (r : Nat) := r + 10
#guard parsem [(1,2),(1,3)] env 1 = 13
#guard parsem [(1,3)] (updateEnv env 1 12) 1 = 13
#guard parsem [(1,2),(1,3)] env 7 = 17
#guard parsem [(1,3)] (updateEnv env 1 12) 7 = 17
#guard parsem [(1,2),(3,1)] env 3 = 11
#guard parsem [(3,1)] (updateEnv env 1 12) 3 = 12
#guard parsem [(1,1),(3,2)] env 3 = 12
#guard parsem [(3,2)] (updateEnv env 1 11) 3 = 12
example : parsem [(1,2),(1,3)] env = parsem [(1,3)] (updateEnv env 1 (env 2)) :=
  parsem_NoRead _ _ _ _ (by simp)
example {α β : Type} [DecidableEq α] (moves : List (α × α)) (x y : α)
    (env : α → β) (h : x ∉ moves.map Prod.snd) :
    parsem ((x,y)::moves) env = parsem moves (updateEnv env x (env y)) :=
  parsem_NoRead moves x y env h
end Flapjack.Test.ParmoveNoReadParity
