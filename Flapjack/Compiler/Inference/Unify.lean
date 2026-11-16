module

public import Flapjack.Compiler.Inference.InferT
public import Flapjack.Misc.Sptree

@[expose] public section

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

/-- Execute the occurs traversal with a list-of-lists worklist, as in the
    source tail-recursive algorithm. `Option` models nontermination. -/
def occursWorkPartial (s : Spt InferT) (n : Nat) (work : List (List InferT)) : Option Bool := do
  match work with
  | [] => some false
  | [] :: rest => occursWorkPartial s n rest
  | (t :: ts) :: rest =>
    match ← walkExecutable s t with
    | .varDb _ => occursWorkPartial s n (ts :: rest)
    | .uvar v => if n == v then some true else occursWorkPartial s n (ts :: rest)
    | .app xs _ => occursWorkPartial s n (xs :: ts :: rest)
partial_fixpoint

/-- Check one type using the unbounded worklist traversal. -/
def occursPartial (s : Spt InferT) (n : Nat) (t : InferT) : Option Bool :=
  occursWorkPartial s n [[t]]

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
equations. The outer option reports worklist fuel exhaustion; the inner option
reports unification failure. Variable walking and the occurs check are
unbounded and can diverge on cyclic substitutions. Preservation of the
well-formedness required for their termination has not yet been proved for
this unifier. -/
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
      if ← occursPartial s x t then some none
      else unifyWorkFuel fuel (sptInsert x t s) rest
    | .varDb x, .varDb y =>
      if x == y then unifyWorkFuel fuel s rest else some none
    | .app xs x, .app ys y =>
      if x == y && xs.length == ys.length then
        unifyWorkFuel fuel s (List.zip xs ys ++ rest)
      else some none
    | _, _ => some none

/-- Unify one pair with a worklist bound. Variable walking and the occurs
check are unbounded, so this is not a total execution bound. -/
def unifyFuel (fuel : Nat) (s : Spt InferT) (a b : InferT) : Option (Option (Spt InferT)) :=
  unifyWorkFuel fuel s [(a, b)]

end Flapjack.Compiler.Inference.Unify
