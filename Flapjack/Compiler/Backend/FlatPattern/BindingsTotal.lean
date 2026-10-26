import Flapjack.Compiler.Backend.FlatPattern.Bindings

/-! Total pattern binding, using a decreasing count of pattern nodes. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.BackendCommon

mutual
/-- Count each pattern node once for the binding worklist measure. -/
private def bindWeight : FlatLang.Pat → Nat
  | .pcon _ ps => 1 + bindWeights ps
  | .pas p _ | .pref p => 1 + bindWeight p
  | _ => 1

private def bindWeights : List FlatLang.Pat → Nat
  | [] => 0
  | p :: ps => bindWeight p + bindWeights ps
end

private def todoWeight : List (FlatLang.Pat × Nat × FlatLang.Exp) → Nat
  | [] => 0
  | (p, _, _) :: rest => bindWeight p + todoWeight rest

private theorem todoWeight_append (xs ys : List (FlatLang.Pat × Nat × FlatLang.Exp)) :
    todoWeight (xs ++ ys) = todoWeight xs + todoWeight ys := by
  induction xs with
  | nil => simp [todoWeight]
  | cons x xs ih => cases x with | mk p pair => cases pair; simp [todoWeight, ih, Nat.add_assoc]

private def patternEntries (t : Tra) (i j : Nat) : List FlatLang.Pat →
    List ((Nat × MlString) × (FlatLang.Pat × Nat × FlatLang.Exp))
  | [] => []
  | p :: ps =>
      let key := i + 1 + j
      let name := encNumToName key
      ((j, name), (p, key, .varLocal t name)) :: patternEntries t i (j + 1) ps

private theorem entriesWeight (t : Tra) (i j : Nat) (ps : List FlatLang.Pat) :
    todoWeight ((patternEntries t i j ps).map Prod.snd) = bindWeights ps := by
  induction ps generalizing j with
  | nil => rfl
  | cons p ps ih => simp [patternEntries, todoWeight, bindWeights, ih]

/-- Bind pattern variables and record which source projections are used. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_pat_bindings_def"]
def compilePatBindings (t : Tra) (i : Nat) (todo : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (exp : FlatLang.Exp) : NumSet × FlatLang.Exp :=
  match todo with
  | [] => (.ln, exp)
  | (p, k, x) :: rest =>
      match p with
      | .pany | .plit _ => compilePatBindings t i rest exp
      | .pvar s =>
          let (used, exp2) := compilePatBindings t i rest exp
          (sptInsert k () used, .let_ t (some s) x exp2)
      | .pcon _ ps =>
          let entries := patternEntries t i 0 ps
          let (used, exp2) := compilePatBindings t (i + 2 + ps.length)
            (entries.map Prod.snd ++ rest) exp
          let selected := entries.filter (fun (_, (_, key, _)) => (sptLookup key used).isSome)
          let exp3 := selected.foldr (fun ((j, name), _) body =>
            .let_ t (some name) (.app t (.el j) [x]) body) exp2
          let used2 := if selected.isEmpty then used else sptInsert k () used
          (used2, exp3)
      | .pas p v =>
          let name := encNumToName (i + 1)
          let (used, exp2) := compilePatBindings t (i + 2)
            ((p, i + 1, .varLocal t name) :: rest) exp
          (sptInsert k () used, .let_ t (some v) x
            (.let_ t (some name) (.varLocal t v) exp2))
      | .pref p =>
          let name := encNumToName (i + 1)
          let (used, exp2) := compilePatBindings t (i + 2)
            ((p, i + 1, .varLocal t name) :: rest) exp
          (sptInsert k () used, .let_ t (some name) (.app t (.el 0) [x]) exp2)
termination_by todoWeight todo
decreasing_by
  all_goals simp_wf
  all_goals simp [todoWeight, bindWeight, todoWeight_append, entriesWeight]
  all_goals omega

/-- Bind variables of a single pattern branch. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_pat_rhs_def"]
def compilePatRhs (t : Tra) (i : Nat) (v : FlatLang.Exp)
    (branch : FlatLang.Pat × FlatLang.Exp) : FlatLang.Exp :=
  (compilePatBindings t (i + 1) [(branch.1, i, v)] branch.2).2

end Flapjack.Compiler.Backend.FlatPattern
