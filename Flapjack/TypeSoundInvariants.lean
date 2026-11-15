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

end
end Flapjack.TypeSoundInvariants
