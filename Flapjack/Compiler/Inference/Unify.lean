module

public import Flapjack.Compiler.Inference.InferT
public import Flapjack.Misc.Sptree

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

@[hol "cakeml/compiler/inference/unifyScript.sml" "cvwalk_code_def"]
def cvwalkCode (s : Spt InferT) (n : Nat) : Sum Nat InferT :=
  match sptLookup n s with
  | none => .inr (.uvar n)
  | some (.uvar u) => .inl u
  | some (.varDb k) => .inr (.varDb k)
  | some (.app ts tc) => .inr (.app ts tc)

/-- Execute the source walker step until it returns a type. This partial
    operation has an `Option` result to model nontermination; the original
    `tcvwalk` returns an `InferT`, so this definition is not tagged as its port. -/
def cvwalkPartial (s : Spt InferT) (n : Nat) : Option InferT :=
  match cvwalkCode s n with
  | .inl u => cvwalkPartial s u
  | .inr t => some t
partial_fixpoint

/-- Walk one type using the unbounded variable walker. -/
def walkExecutable (s : Spt InferT) : InferT → Option InferT
  | .uvar n => cvwalkPartial s n
  | t => some t

mutual
private def occursFuel : Nat → Spt InferT → Nat → InferT → Option Bool
  | 0, _, _, _ => none
  | fuel + 1, s, n, t => do
    match ← walkExecutable s t with
    | .varDb _ => some false
    | .uvar m => some (n == m)
    | .app ts _ => occursListFuel fuel s n ts

private def occursListFuel : Nat → Spt InferT → Nat → List InferT → Option Bool
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => some false
  | fuel + 1, s, n, t :: ts => do
    if ← occursFuel fuel s n t then some true else occursListFuel fuel s n ts
end


mutual
/-- Fully follow a substitution, reporting exhaustion when the structural
fuel runs out. Variable walking is unbounded and may diverge on cyclic inputs. -/
def walkStarFuel : Nat → Spt InferT → InferT → Option InferT
  | 0, _, _ => none
  | fuel + 1, s, t => do
    match ← walkExecutable s t with
    | .varDb n => some (.varDb n)
    | .uvar n => some (.uvar n)
    | .app ts name => (walkStarListFuel fuel s ts).map (InferT.app · name)

def walkStarListFuel : Nat → Spt InferT → List InferT → Option (List InferT)
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | fuel + 1, s, t :: ts => do
    let t ← walkStarFuel fuel s t
    let ts ← walkStarListFuel fuel s ts
    some (t :: ts)
end

/-- A structurally bounded worklist implementation of the source unification
equations. The outer option reports worklist or occurs-check fuel exhaustion;
the inner option reports unification failure. Variable walking is unbounded
and can diverge on cyclic substitutions. Preservation of the well-formedness
required for walker termination has not yet been proved for this unifier. -/
def unifyWorkFuel : Nat → Spt InferT → List (InferT × InferT) → Option (Option (Spt InferT))
  | 0, _, _ => none
  | _ + 1, s, [] => some (some s)
  | fuel + 1, s, (a, b) :: rest => do
    let a ← walkExecutable s a
    let b ← walkExecutable s b
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

/-- Unify one pair with a worklist and occurs-check bound. Variable walking is
unbounded, so this is not a total execution bound for arbitrary substitutions. -/
def unifyFuel (fuel : Nat) (s : Spt InferT) (a b : InferT) : Option (Option (Spt InferT)) :=
  unifyWorkFuel fuel s [(a, b)]

end Flapjack.Compiler.Inference.Unify
