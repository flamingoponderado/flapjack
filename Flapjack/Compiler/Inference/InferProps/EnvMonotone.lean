module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.Compiler.Inference.InferProps.CheckMonotone
public import Flapjack.NamespaceProps.Mono

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer Flapjack.NamespaceHOL

/-- Original `check_env_more`: every entry of a namespace checked against the
first `uvs` unification variables is still checked against a larger bound.
HOL's `count uvs` is the predicate `fun k => k < uvs`. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_env_more"]
theorem ienvValOk_more {M N : Type}
    (env : Namespace M N (Nat × InferT)) (uvs : Nat)
    (h : ienvValOk (fun k => k < uvs) env) :
    ∀ uvs', uvs ≤ uvs' → ienvValOk (fun k => k < uvs') env := by
  intro uvs' hle
  unfold ienvValOk nsAll at h ⊢
  intro id value found
  exact checkTMore4.1 value.2 uvs value.1 (h id value found) uvs' hle

/-- Original `ienv_ok_more`: an inference environment well-formed for the first
`uv` unification variables stays well-formed for a larger bound. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "ienv_ok_more"]
theorem ienvOkMore (uv uv' : Nat) (ienv : Env)
    (h : ienvOk (fun k => k < uv) ienv) (hle : uv ≤ uv') :
    ienvOk (fun k => k < uv') ienv := by
  simp only [ienvOk] at h ⊢
  exact ⟨ienvValOk_more ienv.infV uv h.1 uv' hle, h.2⟩

end Flapjack.Compiler.Inference.InferProps
