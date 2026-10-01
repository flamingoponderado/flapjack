import Flapjack.Compiler.Backend.Parmove.Independence
namespace Flapjack.Test.ParmoveIndependenceParity
open Flapjack.Compiler.Backend.Parmove

-- ind_head=T: equality for every input environment and every queried register.
example : parsem (β := Bool) (([] : List (Nat × Nat)) ++ [(0,1)] ++ [(2,3)]) = parsem ([(0,1)] ++ [] ++ [(2,3)]) :=
  independence [] 1 0 [(2,3)] (([] : List (Nat × Nat)) ++ [(0,1)] ++ [(2,3)]) ⟨by simp [windmill], rfl⟩

-- ind_middle=T: equality for every input environment and every queried register.
example : parsem (β := Nat) (([(0,1)] : List (Nat × Nat)) ++ [(2,3)] ++ [(4,5)]) = parsem ([(2,3)] ++ [(0,1)] ++ [(4,5)]) :=
  independence [(0,1)] 3 2 [(4,5)] (([(0,1)] : List (Nat × Nat)) ++ [(2,3)] ++ [(4,5)]) ⟨by simp [windmill], rfl⟩

-- ind_tail=T: equality for every input environment and every queried register.
example : parsem (β := Bool) (([(0,1),(2,3)] : List (Nat × Nat)) ++ [(4,5)] ++ []) = parsem ([(4,5)] ++ [(0,1),(2,3)] ++ []) :=
  independence [(0,1),(2,3)] 5 4 [] (([(0,1),(2,3)] : List (Nat × Nat)) ++ [(4,5)] ++ []) ⟨by simp [windmill], rfl⟩

-- ind_cycle=T: equality for every input environment and every queried register.
example : parsem (β := Nat) (([(0,1)] : List (Nat × Nat)) ++ [(1,0)] ++ []) = parsem ([(1,0)] ++ [(0,1)] ++ []) :=
  independence [(0,1)] 0 1 [] (([(0,1)] : List (Nat × Nat)) ++ [(1,0)] ++ []) ⟨by simp [windmill], rfl⟩

-- ind_fanout=T: equality for every input environment and every queried register.
example : parsem (β := Bool) (([(0,7)] : List (Nat × Nat)) ++ [(1,7)] ++ [(2,7)]) = parsem ([(1,7)] ++ [(0,7)] ++ [(2,7)]) :=
  independence [(0,7)] 7 1 [(2,7)] (([(0,7)] : List (Nat × Nat)) ++ [(1,7)] ++ [(2,7)]) ⟨by simp [windmill], rfl⟩

-- ind_self=T: equality for every input environment and every queried register.
example : parsem (β := Nat) (([(0,1)] : List (Nat × Nat)) ++ [(2,2)] ++ [(4,5)]) = parsem ([(2,2)] ++ [(0,1)] ++ [(4,5)]) :=
  independence [(0,1)] 2 2 [(4,5)] (([(0,1)] : List (Nat × Nat)) ++ [(2,2)] ++ [(4,5)]) ⟨by simp [windmill], rfl⟩

-- ind_bool=T: equality for every input environment and every queried register.
example : parsem (β := Nat) (([(false,true)] : List (Bool × Bool)) ++ [(true,false)] ++ []) = parsem ([(true,false)] ++ [(false,true)] ++ []) :=
  independence [(false,true)] false true [] (([(false,true)] : List (Bool × Bool)) ++ [(true,false)] ++ []) ⟨by simp [windmill], rfl⟩

-- ind_empty_others=T: equality for every input environment and every queried register.
example : parsem (β := Bool) (([] : List (Bool × Bool)) ++ [(false,true)] ++ []) = parsem ([(false,true)] ++ [] ++ []) :=
  independence [] true false [] (([] : List (Bool × Bool)) ++ [(false,true)] ++ []) ⟨by simp [windmill], rfl⟩

-- ind_nil_nat=T
example : parsem (β := Bool) ([] : List (Nat × Nat)) = id := parsem_nil
-- ind_nil_bool=T
example : parsem (β := Nat) ([] : List (Bool × Bool)) = id := parsem_nil
end Flapjack.Test.ParmoveIndependenceParity
