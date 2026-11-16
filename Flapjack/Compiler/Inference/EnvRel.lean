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

mutual
/-- Closed declarative types convert to inference types with no unification variables.
    The source also quantifies an unused polymorphic `z`; it is vacuous in
    both premise and conclusion. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "check_freevars_to_check_t"]
theorem checkFreevarsToCheckT (t : SemanticT) (n : Nat)
    (h : checkFreevars n [] t = true) :
    Infer.checkT n (fun _ => False) (unconvertT t) := by
  cases t with
  | var name => simp [checkFreevars] at h
  | varDb k => simpa [checkFreevars, unconvertT] using h
  | app ts name =>
    have hl : checkFreevarsList n [] ts = true := by simpa [checkFreevars] using h
    simpa [unconvertT] using checkFreevarsListToCheckT ts n hl
termination_by sizeOf t

/-- Structural list induction for the source type conversion theorem. -/
private theorem checkFreevarsListToCheckT (ts : List SemanticT) (n : Nat)
    (h : checkFreevarsList n [] ts = true) :
    Infer.checkTList n (fun _ => False) (unconvertTList ts) := by
  cases ts with
  | nil => simp [unconvertTList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at h
    simp only [unconvertTList, Infer.checkTList_cons]
    exact ⟨checkFreevarsToCheckT t n h.1, checkFreevarsListToCheckT ts n h.2⟩
termination_by sizeOf ts
end

/-- Lookup in the empty local type environment always fails. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "lookup_varE_empty"]
theorem lookupVarEEmpty (id : Ident Flapjack.Basis.Pure.MlString.MlString
    Flapjack.Basis.Pure.MlString.MlString) : lookupVarE id .empty = none := by
  cases id <;> rfl

end Flapjack.Compiler.Inference.EnvRel
