import Flapjack.Compiler.Backend.Parmove.Correct

namespace Flapjack.Test.ParmoveCorrectParity
open Flapjack.Compiler.Backend.Parmove
-- pc_empty=T: universal environment, exact original premise.
example (env : Option Nat → Nat) : eqenv (seqsem (parmove ([] : List (Nat × Nat))) env) (parsem (([] : List (Nat × Nat)).map fun move => (some move.1, some move.2)) env) :=
  parmove_correct ([] : List (Nat × Nat)) (by simp [windmill]) env
-- pc_self=T: universal environment, exact original premise.
example (env : Option Nat → Nat) : eqenv (seqsem (parmove [(1,1)]) env) (parsem ([(1,1)].map fun move => (some move.1, some move.2)) env) :=
  parmove_correct [(1,1)] (by simp [windmill]) env
-- pc_chain=T: universal environment, exact original premise.
example (env : Option Nat → Nat) : eqenv (seqsem (parmove [(1,2),(2,3)]) env) (parsem ([(1,2),(2,3)].map fun move => (some move.1, some move.2)) env) :=
  parmove_correct [(1,2),(2,3)] (by simp [windmill]) env
-- pc_cycle=T: universal environment, exact original premise.
example (env : Option Nat → Nat) : eqenv (seqsem (parmove [(1,2),(2,1)]) env) (parsem ([(1,2),(2,1)].map fun move => (some move.1, some move.2)) env) :=
  parmove_correct [(1,2),(2,1)] (by simp [windmill]) env
-- pc_fanout=T: universal environment, exact original premise.
example (env : Option Nat → Nat) : eqenv (seqsem (parmove [(1,3),(2,3)]) env) (parsem ([(1,3),(2,3)].map fun move => (some move.1, some move.2)) env) :=
  parmove_correct [(1,3),(2,3)] (by simp [windmill]) env
-- pc_order=T: universal environment, exact original premise.
example (env : Option Nat → Nat) : eqenv (seqsem (parmove [(3,1),(1,2),(2,4)]) env) (parsem ([(3,1),(1,2),(2,4)].map fun move => (some move.1, some move.2)) env) :=
  parmove_correct [(3,1),(1,2),(2,4)] (by simp [windmill]) env
-- pc_bool=T: universal environment, exact original premise.
example (env : Option Bool → Bool) : eqenv (seqsem (parmove [(false,true),(true,false)]) env) (parsem ([(false,true),(true,false)].map fun move => (some move.1, some move.2)) env) :=
  parmove_correct [(false,true),(true,false)] (by simp [windmill]) env

end Flapjack.Test.ParmoveCorrectParity
