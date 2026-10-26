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

private def children (t : Tra) (v : FlatLang.Exp) (j : Nat) : List FlatLang.Pat →
    List (FlatLang.Pat × FlatLang.Exp)
  | [] => []
  | p :: ps => (p, .app t (.el j) [v]) :: children t v (j + 1) ps

private theorem childrenWeight (t : Tra) (v : FlatLang.Exp) (j : Nat) (ps : List FlatLang.Pat) :
    todoWeight (children t v j ps) = naiveWeights ps := by
  induction ps generalizing j with
  | nil => rfl
  | cons p ps ih => simp [children, todoWeight, naiveWeights, ih]

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
          let tail := naivePatternMatch t (children t v 0 ps ++ rest)
          match tag with
          | none => tail
          | some (tag, _) => FlatLang.smartIf t (.app t (.tagLenEq tag ps.length) [v])
              tail (FlatLang.mkBool t false)
      | .pas p _ => naivePatternMatch t ((p, v) :: rest)
      | .pref p => naivePatternMatch t ((p, .app t (.el 0) [v]) :: rest)
termination_by todoWeight todo
decreasing_by
  all_goals simp_wf
  all_goals simp [todoWeight, naiveWeight, todoWeight_append, childrenWeight]
  all_goals omega

/-- Construct the source's ordered naive branch chain. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "naive_pattern_matches_def"]
def naivePatternMatches (t : Tra) (v : FlatLang.Exp) :
    List (FlatLang.Pat × FlatLang.Exp) → FlatLang.Exp → FlatLang.Exp
  | [], default => default
  | (p, x) :: ps, default =>
      FlatLang.smartIf t (naivePatternMatch t [(p, v)]) x (naivePatternMatches t v ps default)

end Flapjack.Compiler.Backend.FlatPattern
