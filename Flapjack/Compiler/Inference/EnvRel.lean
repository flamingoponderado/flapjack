module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.TypeSystemHOL.Declarations

@[expose] public section

/-! Conversions used by the inference/declarative environment relation. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "tenv_to_ienv_def"]
noncomputable def tenvToIenv (env : TypeEnv) : Infer.Env :=
  ⟨nsMap (fun entry => (entry.1, unconvertT entry.2)) env.v, env.c, env.t⟩

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "tenv_to_ienv_lift"]
theorem tenvToIenvLift (mn : Flapjack.Basis.Pure.MlString.MlString) (tenv : TypeEnv) :
    tenvToIenv (tenvLift mn tenv) = Infer.liftIenv mn (tenvToIenv tenv) := by
  cases tenv
  simp [tenvToIenv, tenvLift, Infer.liftIenv, nsLift, nsMap]

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "tenv_to_ienv_extend"]
theorem tenvToIenvExtend (tenv1 tenv2 : TypeEnv) :
    tenvToIenv (extendDecTenv tenv2 tenv1) =
      Infer.extendDecIenv (tenvToIenv tenv2) (tenvToIenv tenv1) := by
  cases tenv1 with
  | mk v1 c1 t1 =>
    cases tenv2 with
    | mk v2 c2 t2 =>
      cases v1 with
      | bind values1 modules1 =>
        cases v2 with
        | bind values2 modules2 =>
          simp [tenvToIenv, extendDecTenv, Infer.extendDecIenv, nsAppend, nsMap, List.map_append]

/-- Lookup in the empty local type environment always fails. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "lookup_varE_empty"]
theorem lookupVarEEmpty (id : Ident Flapjack.Basis.Pure.MlString.MlString
    Flapjack.Basis.Pure.MlString.MlString) : lookupVarE id .empty = none := by
  cases id <;> rfl

end Flapjack.Compiler.Inference.EnvRel
