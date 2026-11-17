module

public import Flapjack.Compiler.Inference.TypeDCanon

@[expose] public section

/-! Renaming type identifiers inside source local environments. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.InferProps

/-- Rename types in local variable bindings without changing their names or scopes. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "remap_tenvE_def"]
def remapTenvE (f : Nat → Nat) : TenvValExp → TenvValExp
  | .empty => .empty
  | .bindTvar tvs env => .bindTvar tvs (remapTenvE f env)
  | .bindName name tvs t env => .bindName name tvs (tsTidRename f t) (remapTenvE f env)

/-- Renaming leaves the local environment's type-variable count unchanged. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "num_tvs_remap_tenvE"]
theorem numTvsRemapTenvE (env : TenvValExp) (f : Nat → Nat) :
    numTvs (remapTenvE f env) = numTvs env := by
  induction env with
  | empty => rfl
  | bindTvar tvs env ih => simp [remapTenvE, numTvs, ih]
  | bindName name tvs t env ih => simp [remapTenvE, numTvs, ih]

/-- Renaming commutes with binding a list of names. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "remap_tenvE_bind_var_list"]
theorem remapTenvEBindVarList (n : Nat) (bindings : List (MlString × SemanticT))
    (env : TenvValExp) (f : Nat → Nat) :
    remapTenvE f (bindVarList n bindings env) =
      bindVarList n (bindings.map (fun entry => (entry.1, tsTidRename f entry.2))) (remapTenvE f env) := by
  induction bindings with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨name, t⟩
    simp [bindVarList, remapTenvE, ih]

/-- Renaming commutes with adding a type-variable binder. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "remap_tenvE_bind_tvar"]
theorem remapTenvEBindTvar (f : Nat → Nat) (tvs : Nat) (env : TenvValExp) :
    remapTenvE f (bindTvar tvs env) = bindTvar tvs (remapTenvE f env) := by
  by_cases h : tvs = 0 <;> simp [bindTvar, remapTenvE, h]

mutual
/-- Type-ID renaming commutes with incrementing de Bruijn indices. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "deBruijn_inc_ts_tid_rename"]
theorem deBruijnIncTsTidRename (skip amount : Nat) (t : SemanticT) (f : Nat → Nat) :
    tsTidRename f (deBruijnInc skip amount t) = deBruijnInc skip amount (tsTidRename f t) := by
  cases t with
  | var name => simp [deBruijnInc, tsTidRename]
  | varDb n => simp [deBruijnInc, tsTidRename]
  | app ts id => simp [deBruijnInc, tsTidRename, deBruijnIncListTsTidRename skip amount ts f]
termination_by sizeOf t

private theorem deBruijnIncListTsTidRename (skip amount : Nat) (ts : List SemanticT) (f : Nat → Nat) :
    tsTidRenameList f (deBruijnIncList skip amount ts) =
      deBruijnIncList skip amount (tsTidRenameList f ts) := by
  cases ts with
  | nil => simp [deBruijnIncList, tsTidRenameList]
  | cons t ts =>
    simp [deBruijnIncList, tsTidRenameList, deBruijnIncTsTidRename skip amount t f,
      deBruijnIncListTsTidRename skip amount ts f]
termination_by sizeOf ts
end

/-- The local lookup induction used by the source lookup-renaming theorem. -/
private theorem tveLookupRemapTenvE (name : MlString) (inc : Nat) (env : TenvValExp)
    (f : Nat → Nat) :
    tveLookup name inc (remapTenvE f env) =
      (tveLookup name inc env).map (fun entry => (entry.1, tsTidRename f entry.2)) := by
  induction env generalizing inc with
  | empty => rfl
  | bindTvar tvs env ih => simp [remapTenvE, tveLookup, ih]
  | bindName name' tvs t env ih =>
    by_cases same : name' = name
    · simp [remapTenvE, tveLookup, same, deBruijnIncTsTidRename]
    · simp [remapTenvE, tveLookup, same, ih]

/-- Lookup in a renamed local environment renames the returned type. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "lookup_varE_remap_tenvE"]
theorem lookupVarERemapTenvE (name : Ident MlString MlString) (env : TenvValExp)
    (f : Nat → Nat) :
    lookupVarE name (remapTenvE f env) =
      (lookupVarE name env).map (fun entry => (entry.1, tsTidRename f entry.2)) := by
  cases name with
  | short name => exact tveLookupRemapTenvE name 0 env f
  | long name rest => rfl

mutual
/-- Type-ID renaming commutes with de Bruijn substitution. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "ts_tid_rename_deBruijn_subst"]
theorem tsTidRenameDeBruijnSubst (n : Nat) (args : List SemanticT) (t : SemanticT) (f : Nat → Nat) :
    tsTidRename f (deBruijnSubst n args t) =
      deBruijnSubst n (args.map (tsTidRename f)) (tsTidRename f t) := by
  cases t with
  | var name => simp [deBruijnSubst, tsTidRename]
  | varDb id =>
    by_cases inside : n ≤ id ∧ id < args.length + n
    · simp [deBruijnSubst, tsTidRename, inside]
    · by_cases above : n ≤ id
      · have outside : ¬ id < args.length + n := fun h => inside ⟨above, h⟩
        simp [deBruijnSubst, tsTidRename, above, outside]
      · simp [deBruijnSubst, tsTidRename, above]
  | app ts id => simp [deBruijnSubst, tsTidRename, tsTidRenameDeBruijnSubstList n args ts f]
termination_by sizeOf t

private theorem tsTidRenameDeBruijnSubstList (n : Nat) (args ts : List SemanticT) (f : Nat → Nat) :
    tsTidRenameList f (deBruijnSubstList n args ts) =
      deBruijnSubstList n (args.map (tsTidRename f)) (tsTidRenameList f ts) := by
  cases ts with
  | nil => simp [deBruijnSubstList, tsTidRenameList]
  | cons t ts =>
    simp [deBruijnSubstList, tsTidRenameList, tsTidRenameDeBruijnSubst n args t f,
      tsTidRenameDeBruijnSubstList n args ts f]
termination_by sizeOf ts
end

end Flapjack.Compiler.Inference.TypeDCanon
