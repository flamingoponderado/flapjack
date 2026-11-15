module

public import Flapjack.Compiler.Inference.InferProps

@[expose] public section

/-! Conversions used by the inference/declarative environment relation. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "tenv_to_ienv_def"]
noncomputable def tenvToIenv (env : TypeEnv) : Infer.Env :=
  ⟨nsMap (fun entry => (entry.1, unconvertT entry.2)) env.v, env.c, env.t⟩

/-- Lookup in the empty local type environment always fails. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "lookup_varE_empty"]
theorem lookupVarEEmpty (id : Ident Flapjack.Basis.Pure.MlString.MlString
    Flapjack.Basis.Pure.MlString.MlString) : lookupVarE id .empty = none := by
  cases id <;> rfl

end Flapjack.Compiler.Inference.EnvRel
