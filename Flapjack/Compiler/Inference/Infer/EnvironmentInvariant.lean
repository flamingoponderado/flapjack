module

public import Flapjack.Compiler.Inference.InferT
public import Flapjack.NamespaceHOL
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Inference-type and namespace checks used by the environment relation. -/
namespace Flapjack.Compiler.Inference.Infer
open Flapjack.NamespaceHOL

mutual
@[hol "cakeml/compiler/inference/inferScript.sml" "check_t_def"]
def checkT (n : Nat) (uvars : Nat → Prop) : InferT → Prop
  | .uvar v => uvars v
  | .varDb v => v < n
  | .app ts _ => checkTList n uvars ts
termination_by t => sizeOf t

/-- List traversal for the original `EVERY` clause of `checkT`. -/
def checkTList (n : Nat) (uvars : Nat → Prop) : List InferT → Prop
  | [] => True
  | t :: ts => checkT n uvars t ∧ checkTList n uvars ts
termination_by ts => sizeOf ts
end

/-- Expose the recursive check equations to downstream proofs; the underlying
well-founded mutual definition implements the HOL clauses above. -/
@[simp] theorem checkT_uvar (n v : Nat) (uvars : Nat → Prop) :
    checkT n uvars (.uvar v) ↔ uvars v := by simp [checkT]

@[simp] theorem checkT_varDb (n v : Nat) (uvars : Nat → Prop) :
    checkT n uvars (.varDb v) ↔ v < n := by simp [checkT]

@[simp] theorem checkT_app (n tag : Nat) (uvars : Nat → Prop) (ts : List InferT) :
    checkT n uvars (.app ts tag) ↔ checkTList n uvars ts := by simp [checkT]

@[simp] theorem checkTList_nil (n : Nat) (uvars : Nat → Prop) :
    checkTList n uvars [] ↔ True := by simp [checkTList]

@[simp] theorem checkTList_cons (n : Nat) (uvars : Nat → Prop) (t : InferT) (ts : List InferT) :
    checkTList n uvars (t :: ts) ↔ checkT n uvars t ∧ checkTList n uvars ts := by simp [checkTList]

/-- Original `check_s_def`: every value in the substitution's domain passes the
    type check. HOL's `FDOM` membership is a successful lookup and `s⟨uv⟩` is
    the map's total application, rendered with the `.varDb 0` default that
    `inferTypeSubst` uses for `FAPPLY` outside the map's domain. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "check_s_def"
  (fmap_as_finite_support_parameters := [s])]
def checkS {α : Type} (tvs : Nat) (uvs : Nat → Prop) (s : HolFiniteMapExact α InferT) : Prop :=
  ∀ uv, s.lookup uv ≠ none → checkT tvs uvs ((s.lookup uv).getD (.varDb 0))

/-- The canonical substitution map survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_checkS_s {α : Type}
    (s : HolFiniteMapExact α InferT) (key : α) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s := by
  cases s
  exact ⟨rfl, rfl, rfl⟩

noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

@[hol "cakeml/compiler/inference/inferScript.sml" "ienv_val_ok_def"]
def ienvValOk {M N : Type} (uvars : Nat → Prop) (env : Namespace M N (Nat × InferT)) : Prop :=
  nsAll (fun _ entry => checkT entry.1 uvars entry.2) env

end
end Flapjack.Compiler.Inference.Infer
