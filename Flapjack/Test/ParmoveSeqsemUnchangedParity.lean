import Flapjack.Compiler.Backend.Parmove.SeqsemUnchanged

namespace Flapjack.Test.ParmoveSeqsemUnchangedParity
open Flapjack.Compiler.Backend.Parmove
private def env (key : Nat) := key + 10

-- su_empty=(19,T)
example : (seqsem [] env 9, decide (seqsem [] env 9 = env 9)) = (19,true) := by
  simp [seqsem, env]

-- su_chain=(19,T)
example : (seqsem [(1,2), (2,3)] env 9, decide (seqsem [(1,2), (2,3)] env 9 = env 9)) = (19,true) := by
  simp [seqsem, updateEnv, env]

-- su_cycle=(19,T)
example : (seqsem [(1,2), (2,1)] env 9, decide (seqsem [(1,2), (2,1)] env 9 = env 9)) = (19,true) := by
  simp [seqsem, updateEnv, env]

-- su_repeat=(19,T)
example : (seqsem [(1,2), (1,3)] env 9, decide (seqsem [(1,2), (1,3)] env 9 = env 9)) = (19,true) := by
  simp [seqsem, updateEnv, env]

-- su_source=(19,T)
example : (seqsem [(1,9)] env 9, decide (seqsem [(1,9)] env 9 = env 9)) = (19,true) := by
  simp [seqsem, updateEnv, env]

-- su_written=(12,F)
example : (seqsem [(1,2)] env 1, decide (seqsem [(1,2)] env 1 = env 1)) = (12,false) := by
  simp [seqsem, updateEnv, env]

-- su_self=(11,T)
example : (seqsem [(1,1)] env 1, decide (seqsem [(1,1)] env 1 = env 1)) = (11,true) := by
  simp [seqsem, updateEnv, env]

example {α β : Type} [DecidableEq α] (ms : List (α × α)) (r : α → β)
    (k : α) (h : k ∉ ms.map Prod.fst) := seqsemMoveUnchanged ms r k h

private def boolEnv : Bool → Nat := fun b => if b then 7 else 3
example : (seqsem [(true,false)] boolEnv false, decide (seqsem [(true,false)] boolEnv false = boolEnv false)) = (3,true) := by
  simp [seqsem, updateEnv, boolEnv]

end Flapjack.Test.ParmoveSeqsemUnchangedParity
