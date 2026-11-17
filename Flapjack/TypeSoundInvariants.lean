module

public import Flapjack.TypeSystemHOL.Environments

@[expose] public section

/-! Declarative type-environment well-formedness used by compiler correctness. -/
namespace Flapjack.TypeSoundInvariants
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.TypeSystemHOL

noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "tenv_abbrev_ok_def"]
def tenvAbbrevOk {M N : Type} (env : Namespace M N (List MlString × SemanticT)) : Prop :=
  nsAll (fun _ entry => checkFreevars 0 entry.1 entry.2 = true) env

@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "tenv_ctor_ok_def"]
def tenvCtorOk {M N Tag : Type} (env : Namespace M N (List MlString × List SemanticT × Tag)) : Prop :=
  nsAll (fun _ entry => ∀ t ∈ entry.2.1, checkFreevars 0 entry.1 t = true) env

@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "tenv_val_ok_def"]
def tenvValOk {M N : Type} (env : Namespace M N (Nat × SemanticT)) : Prop :=
  nsAll (fun _ entry => checkFreevars entry.1 [] entry.2 = true) env

@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "tenv_ok_def"]
def tenvOk (env : TypeEnv) : Prop :=
  tenvValOk env.v ∧ tenvCtorOk env.c ∧ tenvAbbrevOk env.t

/-- Check free type variables throughout the local value environment. -/
@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "tenv_val_exp_ok_def"]
def tenvValExpOk : TenvValExp → Prop
  | .empty => True
  | .bindTvar _ env => tenvValExpOk env
  | .bindName _ tvs t env =>
      checkFreevars (tvs + numTvs env) [] t = true ∧ tenvValExpOk env

/-- Add the named local value bindings to a type namespace. -/
@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "add_tenvE_def"]
def addTenvE {M : Type} : TenvValExp → Namespace M MlString (Nat × SemanticT) →
    Namespace M MlString (Nat × SemanticT)
  | .empty, env => env
  | .bindTvar _ localEnv, env => addTenvE localEnv env
  | .bindName name tvs t localEnv, env =>
      nsBind name (tvs, t) (addTenvE localEnv env)

end
end Flapjack.TypeSoundInvariants
