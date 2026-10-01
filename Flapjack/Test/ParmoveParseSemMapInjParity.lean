import Flapjack.Compiler.Backend.Parmove.ParseSemMapInj

namespace Flapjack.Test.ParmoveParseSemMapInjParity
open Flapjack.Compiler.Backend.Parmove
private def rename (n : Nat) := n + 10
private def env (n : Nat) := n + 10

-- pi_one=(21,21,T)
example : (parsem ([(0,1)].map (fun m => (rename m.1,rename m.2))) env (rename 0), parsem [(0,1)] (env ∘ rename) 0) = (21,21) := by
  simp [parsem, updateEnvList, updateEnv, rename, env, Function.comp_def]

-- pi_chain=(21,21,T)
example : (parsem ([(0,1), (1,2)].map (fun m => (rename m.1,rename m.2))) env (rename 0), parsem [(0,1), (1,2)] (env ∘ rename) 0) = (21,21) := by
  simp [parsem, updateEnvList, updateEnv, rename, env, Function.comp_def]

-- pi_cycle=(20,20,T)
example : (parsem ([(0,1), (1,0)].map (fun m => (rename m.1,rename m.2))) env (rename 1), parsem [(0,1), (1,0)] (env ∘ rename) 1) = (20,20) := by
  simp [parsem, updateEnvList, updateEnv, rename, env, Function.comp_def]

-- pi_shared_source=(22,22,T)
example : (parsem ([(0,2), (1,2)].map (fun m => (rename m.1,rename m.2))) env (rename 1), parsem [(0,2), (1,2)] (env ∘ rename) 1) = (22,22) := by
  simp [parsem, updateEnvList, updateEnv, rename, env, Function.comp_def]

-- pi_self=(20,20,T)
example : (parsem ([(0,0)].map (fun m => (rename m.1,rename m.2))) env (rename 0), parsem [(0,0)] (env ∘ rename) 0) = (20,20) := by
  simp [parsem, updateEnvList, updateEnv, rename, env, Function.comp_def]

-- pi_high=(23,23,T)
example : (parsem ([(1000000000000000000000000,3)].map (fun m => (rename m.1,rename m.2))) env (rename 1000000000000000000000000), parsem [(1000000000000000000000000,3)] (env ∘ rename) 1000000000000000000000000) = (23,23) := by
  simp [parsem, updateEnvList, updateEnv, rename, env, Function.comp_def]

example {α γ β : Type} [DecidableEq α] [DecidableEq γ]
    (ms : List (α × α)) (f : α → γ) (r : γ → β)
    (w : windmill ms)
    (hi : ∀ a ∈ ms.map Prod.fst ++ ms.map Prod.snd,
      ∀ b ∈ ms.map Prod.fst ++ ms.map Prod.snd, f a = f b → a = b)
    (x : α) (h : x ∈ ms.map Prod.fst) := parsemMapInj ms f r w hi x h

private def boolRename (n : Nat) : Bool := decide (n = 0)
private def boolEnv (b : Bool) : Nat := if b then 7 else 3
-- pi_mixed=(3,3,T): renaming is not globally injective.
example : (parsem ([(0,1)].map (fun m => (boolRename m.1,boolRename m.2))) boolEnv (boolRename 0),
    parsem [(0,1)] (boolEnv ∘ boolRename) 0) = (3,3) := by
  simp [parsem, updateEnvList, updateEnv, boolRename, boolEnv, Function.comp_def]
-- pi_collision=(10,11,F): domain injectivity is necessary.
example : (parsem ([(0,1),(2,2)].map (fun m => (m.1 % 2,m.2 % 2))) env 0,
    parsem [(0,1),(2,2)] (fun n => env (n % 2)) 0) = (10,11) := by
  simp [parsem, updateEnvList, updateEnv, env]

end Flapjack.Test.ParmoveParseSemMapInjParity
