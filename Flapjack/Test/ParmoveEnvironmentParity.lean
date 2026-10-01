import Flapjack.Compiler.Backend.Parmove.EnvironmentChange
namespace Flapjack.Test.ParmoveEnvironmentParity
open Flapjack.Compiler.Backend.Parmove
private def first (r : Nat) := r + 10
private def second (r : Nat) := if r = 2 then 12 else 99
#guard parsem [(1,2),(1,2)] first 1 = 12
#guard parsem [(1,2),(1,2)] second 1 = 12
#guard parsem [(1,2),(1,2)] first 7 = 17
#guard parsem [(1,2),(1,2)] second 7 = 99
#guard parsem [(1,2),(1,2)] (fun r => if r = 2 then 100 else 99) 1 = 100
#guard [(1,2),(1,2)].map (first ∘ Prod.snd) = [(1,2),(1,2)].map (second ∘ Prod.snd)
#guard parsem [] first 7 = 17
#guard parsem [(1,2),(3,1)] first 3 = 11
example : parsem [(1,2),(1,2)] first 1 = parsem [(1,2),(1,2)] second 1 := by
  apply parsem_change_env
  constructor
  · simp
  · rfl
example {α β : Type} [DecidableEq α] (moves : List (α × α))
    (first second : α → β) (key : α)
    (h : (key ∉ moves.map Prod.fst → first key = second key) ∧
      moves.map (first ∘ Prod.snd) = moves.map (second ∘ Prod.snd)) :
    parsem moves first key = parsem moves second key := parsem_change_env moves first second key h
end Flapjack.Test.ParmoveEnvironmentParity
