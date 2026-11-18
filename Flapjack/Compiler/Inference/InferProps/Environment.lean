module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.NamespaceProps

@[expose] public section

/-! Basic laws for inference environments. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer Flapjack.NamespaceHOL

/-- Updating an inference-environment field with its current value is an identity. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "ienv_unchanged"]
theorem ienvUnchanged (env : Env) :
    { env with infV := env.infV } = env ∧
      { env with infC := env.infC } = env ∧
      { env with infT := env.infT } = env := by
  cases env
  exact ⟨rfl, rfl, rfl⟩

/-- Empty inference environments are two-sided identities for extension. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "extend_dec_ienv_empty"]
theorem extendDecIenvEmpty : ∀ env : Env,
    extendDecIenv env ⟨nsEmpty, nsEmpty, nsEmpty⟩ = env ∧
      extendDecIenv ⟨nsEmpty, nsEmpty, nsEmpty⟩ env = env := by
  intro ⟨v, c, t⟩
  simp [extendDecIenv, (nsAppend_nsEmpty _).1, (nsAppend_nsEmpty _).2]

end Flapjack.Compiler.Inference.InferProps
