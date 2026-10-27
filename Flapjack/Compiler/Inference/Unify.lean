import Flapjack.Compiler.Inference.InferT
import Flapjack.Misc.Sptree

/-! Executable inference-type substitutions and bounded unification. -/
namespace Flapjack.Compiler.Inference.Unify

mutual
@[hol "cakeml/compiler/inference/unifyScript.sml" "capply_subst_def"]
def applySubst (s : Spt InferT) : InferT → InferT
  | .varDb n => .varDb n
  | .uvar n => (sptLookup n s).getD (.uvar n)
  | .app ts name => .app (applySubstList s ts) name
termination_by t => sizeOf t

/-- List traversal for `applySubst`; infrastructure for the HOL `MAP` clause. -/
def applySubstList (s : Spt InferT) : List InferT → List InferT
  | [] => []
  | t :: ts => applySubst s t :: applySubstList s ts
termination_by ts => sizeOf ts
end

/-- Follow variable bindings. `none` means the supplied fuel was exhausted. -/
def walkFuel : Nat → Spt InferT → InferT → Option InferT
  | 0, _, _ => none
  | fuel + 1, s, .uvar n => match sptLookup n s with
    | none => some (.uvar n)
    | some t => walkFuel fuel s t
  | _ + 1, _, t => some t

mutual
private def occursFuel : Nat → Spt InferT → Nat → InferT → Option Bool
  | 0, _, _, _ => none
  | fuel + 1, s, n, t => do
    match ← walkFuel (fuel + 1) s t with
    | .varDb _ => some false
    | .uvar m => some (n == m)
    | .app ts _ => occursListFuel fuel s n ts

private def occursListFuel : Nat → Spt InferT → Nat → List InferT → Option Bool
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => some false
  | fuel + 1, s, n, t :: ts => do
    if ← occursFuel fuel s n t then some true else occursListFuel fuel s n ts
end

/-- A finite worklist implementation of the source unification equations.
The outer option reports fuel exhaustion; the inner option reports unification
failure. This is Flapjack infrastructure until its correspondence with HOL's
unbounded, well-formed-substitution algorithm is established. -/
def unifyWorkFuel : Nat → Spt InferT → List (InferT × InferT) → Option (Option (Spt InferT))
  | 0, _, _ => none
  | _ + 1, s, [] => some (some s)
  | fuel + 1, s, (a, b) :: rest => do
    let a ← walkFuel (fuel + 1) s a
    let b ← walkFuel (fuel + 1) s b
    match a, b with
    | .uvar x, .uvar y =>
      unifyWorkFuel fuel (if x == y then s else sptInsert x (.uvar y) s) rest
    | .uvar x, t | t, .uvar x =>
      if ← occursFuel fuel s x t then some none
      else unifyWorkFuel fuel (sptInsert x t s) rest
    | .varDb x, .varDb y =>
      if x == y then unifyWorkFuel fuel s rest else some none
    | .app xs x, .app ys y =>
      if x == y && xs.length == ys.length then
        unifyWorkFuel fuel s (List.zip xs ys ++ rest)
      else some none
    | _, _ => some none

/-- Unify one pair with an explicit execution bound. -/
def unifyFuel (fuel : Nat) (s : Spt InferT) (a b : InferT) : Option (Option (Spt InferT)) :=
  unifyWorkFuel fuel s [(a, b)]

end Flapjack.Compiler.Inference.Unify
