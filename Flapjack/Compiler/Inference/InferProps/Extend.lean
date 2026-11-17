module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.NamespaceProps

@[expose] public section

/-! Well-formed inference environments are closed under declaration extension. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer Flapjack.NamespaceHOL Flapjack.TypeSoundInvariants

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "ienv_ok_extend_dec_ienv"]
theorem ienvOkExtendDecIenv (e1 e2 : Env) (n : Nat → Prop)
    (h : ienvOk n e1 ∧ ienvOk n e2) : ienvOk n (extendDecIenv e1 e2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.1, h.2.1⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.2.1, h.2.2.1⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.2.2, h.2.2.2⟩

end Flapjack.Compiler.Inference.InferProps
