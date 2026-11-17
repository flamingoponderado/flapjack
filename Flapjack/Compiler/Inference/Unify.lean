module

public import Flapjack.Compiler.Inference.InferT
public import Flapjack.Misc.Sptree

@[expose] public section

/-! Executable inference-type substitutions and unification. -/
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

@[hol "cakeml/compiler/inference/unifyScript.sml" "kclkont"]
inductive KclKont where
  | db : Nat → KclKont
  | app : List InferT → Nat → KclKont
  | uv : Nat → KclKont
  | cons : List InferT → Nat → KclKont

/-- The source normalization worklist, with `Option` recording possible
    nontermination. Its continuation frames are processed in tail position. -/
def walkStarWork (s : Spt InferT) (ready : Bool)
    (items : List InferT) (kont : List KclKont) : Option (List InferT) := do
  if ready then
    match kont with
    | [] => some items
    | .db n :: ks => walkStarWork s true (.varDb n :: items) ks
    | .app args n :: ks => walkStarWork s true (.app args n :: items) ks
    | .uv n :: ks => walkStarWork s true (.uvar n :: items) ks
    | .cons rest n :: ks => walkStarWork s false rest (.app items n :: ks)
  else
    match items with
    | [] => walkStarWork s true [] kont
    | .varDb n :: rest => walkStarWork s false rest (.db n :: kont)
    | .app args n :: rest => walkStarWork s false args (.cons rest n :: kont)
    | .uvar v :: rest =>
      match ← cvwalkPartial s v with
      | .varDb n => walkStarWork s false rest (.db n :: kont)
      | .app args n => walkStarWork s false args (.cons rest n :: kont)
      | .uvar u => walkStarWork s false rest (.uv u :: kont)
partial_fixpoint

/-- Normalize a list with the unbounded source worklist. -/
def walkStarList (s : Spt InferT) (ts : List InferT) : Option (List InferT) :=
  walkStarWork s false ts []

/-- Normalize one type with the unbounded source worklist. -/
def walkStar (s : Spt InferT) (t : InferT) : Option InferT := do
  let ts ← walkStarList s [t]
  ts.head?

/-- Execute the source paired-list unification worklist. The outer option
models nontermination, while the inner option reports unification failure.
The total HOL operation has no outer option, so this definition is untagged;
`Unify.WorklistTotal` proves termination under the original cwfs guard. -/
def unifyWorkPartial (s : Spt InferT) (work : List (List InferT × List InferT)) :
    Option (Option (Spt InferT)) := do
  match work with
  | [] => some (some s)
  | ([], []) :: rest => unifyWorkPartial s rest
  | ([], _ :: _) :: _ | (_ :: _, []) :: _ => some none
  | (a :: left, b :: right) :: rest =>
    let a ← walkExecutable s a
    let b ← walkExecutable s b
    match a, b with
    | .uvar x, .uvar y =>
      unifyWorkPartial (if x == y then s else sptInsert x (.uvar y) s) ((left, right) :: rest)
    | .uvar x, .varDb y | .varDb y, .uvar x =>
      unifyWorkPartial (sptInsert x (.varDb y) s) ((left, right) :: rest)
    | .uvar x, .app ts name | .app ts name, .uvar x =>
      if ← occursWorkPartial s x [ts] then some none
      else unifyWorkPartial (sptInsert x (.app ts name) s) ((left, right) :: rest)
    | .varDb x, .varDb y =>
      if x == y then unifyWorkPartial s ((left, right) :: rest) else some none
    | .app xs x, .app ys y =>
      if x == y then
        unifyWorkPartial s ((xs, ys) :: (left, right) :: rest)
      else some none
    | _, _ => some none
partial_fixpoint

/-- Unify one pair using the source worklist shape. -/
def unifyPartial (s : Spt InferT) (a b : InferT) : Option (Option (Spt InferT)) :=
  unifyWorkPartial s [([a], [b])]

end Flapjack.Compiler.Inference.Unify
