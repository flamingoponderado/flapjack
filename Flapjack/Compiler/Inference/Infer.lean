import Flapjack.Compiler.Inference.InferT
import Flapjack.TypeSystemHOL
import Flapjack.Misc.Sptree
import Flapjack.NamespaceHOL

/-! Substitution and generalization operations used by CakeML inference. -/
namespace Flapjack.Compiler.Inference.Infer
open Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString

mutual
@[hol "cakeml/compiler/inference/inferScript.sml" "infer_type_subst_def"]
def inferTypeSubst (s : List (MlString × InferT)) : TypeSystemHOL.SemanticT → InferT
  | .var v => (s.lookup v).getD (.varDb 0)
  | .varDb n => .varDb n
  | .app ts name => .app (inferTypeSubstList s ts) name
termination_by t => sizeOf t

@[hol "cakeml/compiler/inference/inferScript.sml" "infer_type_subst_def"]
def inferTypeSubstList (s : List (MlString × InferT)) : List TypeSystemHOL.SemanticT → List InferT
  | [] => []
  | t :: ts => inferTypeSubst s t :: inferTypeSubstList s ts
termination_by ts => sizeOf ts
end

mutual
@[hol "cakeml/compiler/inference/inferScript.sml" "infer_deBruijn_subst_def"]
def inferDeBruijnSubst (s : List InferT) : InferT → InferT
  | .varDb n => (s[n]?).getD (.varDb (n - s.length))
  | .app ts name => .app (inferDeBruijnSubstList s ts) name
  | .uvar n => .uvar n
termination_by t => sizeOf t

@[hol "cakeml/compiler/inference/inferScript.sml" "infer_deBruijn_subst_def"]
def inferDeBruijnSubstList (s : List InferT) : List InferT → List InferT
  | [] => []
  | t :: ts => inferDeBruijnSubst s t :: inferDeBruijnSubstList s ts
termination_by ts => sizeOf ts
end

/- Executable generalization with a sparse-tree substitution. The HOL source
uses a finite map, so this infrastructure remains untagged until that map
translation and the function's correspondence have been established. -/
mutual
 def generalise (minimum next : Nat) (subst : Spt Nat) : InferT → Nat × Spt Nat × InferT
  | .app ts name =>
    let (count, subst, ts) := generaliseList minimum next subst ts
    (count, subst, .app ts name)
  | .uvar n => match sptLookup n subst with
    | some v => (0, subst, .varDb v)
    | none => if minimum ≤ n then (1, sptInsert n next subst, .varDb next) else (0, subst, .uvar n)
  | .varDb n => (0, subst, .varDb n)
termination_by t => sizeOf t

 def generaliseList (minimum next : Nat) (subst : Spt Nat) : List InferT → Nat × Spt Nat × List InferT
  | [] => (0, subst, [])
  | t :: ts =>
    let (count, subst, t) := generalise minimum next subst t
    let (count', subst, ts) := generaliseList minimum (count + next) subst ts
    (count + count', subst, t :: ts)
termination_by ts => sizeOf ts
end



/-- CakeML's inference environment, with independent value, constructor,
and type-abbreviation namespaces. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "inf_env"]
structure Env where
  infV : Flapjack.NamespaceHOL.Namespace MlString MlString (Nat × InferT)
  infC : Flapjack.NamespaceHOL.Namespace MlString MlString
    (List MlString × List TypeSystemHOL.SemanticT × Nat)
  infT : Flapjack.NamespaceHOL.Namespace MlString MlString
    (List MlString × TypeSystemHOL.SemanticT)

def emptyEnv : Env := ⟨Flapjack.NamespaceHOL.nsEmpty, Flapjack.NamespaceHOL.nsEmpty,
  Flapjack.NamespaceHOL.nsEmpty⟩

/-- Executable inference state using sparse-tree substitutions. HOL uses a
finite map, so this carrier and its operations are Flapjack infrastructure
until the representation correspondence has been established. -/
structure State where
  nextUvar : Nat
  subst : Spt InferT
  nextId : Nat
  deriving Repr

def freshUvar (s : State) : InferT × State :=
  (.uvar s.nextUvar, { s with nextUvar := s.nextUvar + 1 })

def freshUvars (n : Nat) (s : State) : List InferT × State :=
  (List.ofFn (n := n) (fun i => .uvar (s.nextUvar + i.val)),
   { s with nextUvar := s.nextUvar + n })

def freshIds (n : Nat) (s : State) : List Nat × State :=
  (List.ofFn (n := n) (fun i => s.nextId + i.val), { s with nextId := s.nextId + n })

def resetState (s : State) : State :=
  { s with nextUvar := 0, subst := .ln }

end Flapjack.Compiler.Inference.Infer
