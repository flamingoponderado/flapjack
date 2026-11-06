import Flapjack.Compiler.Backend.FlatPattern.BindingsTotal

/-! Total naive pattern matching, justified by the number of pattern nodes. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.BackendCommon

mutual
private def naiveWeight : FlatLang.Pat → Nat
  | .pcon _ ps => 1 + naiveWeights ps
  | .pas p _ | .pref p => 1 + naiveWeight p
  | _ => 1

private def naiveWeights : List FlatLang.Pat → Nat
  | [] => 0
  | p :: ps => naiveWeight p + naiveWeights ps
end

private def todoWeight : List (FlatLang.Pat × FlatLang.Exp) → Nat
  | [] => 0
  | (p, _) :: rest => naiveWeight p + todoWeight rest

private theorem todoWeight_append (xs ys : List (FlatLang.Pat × FlatLang.Exp)) :
    todoWeight (xs ++ ys) = todoWeight xs + todoWeight ys := by
  induction xs with
  | nil => simp [todoWeight]
  | cons x xs ih => cases x; simp [todoWeight, ih, Nat.add_assoc]

private theorem todoWeight_eq (todo : List (FlatLang.Pat × FlatLang.Exp)) :
    todoWeight todo = naiveWeights (todo.map Prod.fst) := by
  induction todo with
  | nil => rfl
  | cons pair rest ih => cases pair; simp [todoWeight, naiveWeights, ih]

/-- Indexed projections preserve the original pattern list. -/
theorem mapIdx_pair_fst {α β : Type} (f : Nat → β) (ps : List α) :
    (ps.mapIdx fun i p => (p, f i)).map Prod.fst = ps := by
  apply List.ext_getElem <;> simp [List.getElem_mapIdx]

private theorem mapIdxWeight (f : Nat → FlatLang.Exp) (ps : List FlatLang.Pat) :
    todoWeight (ps.mapIdx fun i p => (p, f i)) = naiveWeights ps := by
  rw [todoWeight_eq, mapIdx_pair_fst]

/-- Construct the source's naive match guard. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "naive_pattern_match_def"]
def naivePatternMatch (t : Tra) (todo : List (FlatLang.Pat × FlatLang.Exp)) : FlatLang.Exp :=
  match todo with
  | [] => FlatLang.mkBool t true
  | (p, v) :: rest =>
      match p with
      | .pany | .pvar _ => naivePatternMatch t rest
      | .plit l => FlatLang.smartIf t (.app t (.src .equality) [v, .lit t l])
          (naivePatternMatch t rest) (FlatLang.mkBool t false)
      | .pcon tag ps =>
          let tail := naivePatternMatch t (ps.mapIdx (fun i p => (p, .app t (.el i) [v])) ++ rest)
          match tag with
          | none => tail
          | some (tag, _) => FlatLang.smartIf t (.app t (.tagLenEq tag ps.length) [v])
              tail (FlatLang.mkBool t false)
      | .pas p _ => naivePatternMatch t ((p, v) :: rest)
      | .pref p => naivePatternMatch t ((p, .app t (.el 0) [v]) :: rest)
termination_by todoWeight todo
decreasing_by
  all_goals simp_wf
  all_goals simp [todoWeight, naiveWeight, todoWeight_append, mapIdxWeight]
  all_goals omega

/-- Construct the source's ordered naive branch chain. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "naive_pattern_matches_def"]
def naivePatternMatches (t : Tra) (v : FlatLang.Exp) :
    List (FlatLang.Pat × FlatLang.Exp) → FlatLang.Exp → FlatLang.Exp
  | [], default => default
  | (p, x) :: ps, default =>
      FlatLang.smartIf t (naivePatternMatch t [(p, v)]) x (naivePatternMatches t v ps default)

end Flapjack.Compiler.Backend.FlatPattern
