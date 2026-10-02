import Flapjack.FfiHOL

namespace Flapjack

/-- HOL's single successful FFI-call relation. All four witnesses are retained:
the name, configuration, input bytes, and returned bytes. This is the step
relation, rather than its reflexive-transitive closure. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "call_FFI_rel_def"]
def callFFIRelHOL {σ : Type} (before after : HolFfiState σ) : Prop :=
  ∃ (name : HolFfiName) (configuration bytes returned : List (BitVec 8)),
    callFFIHOL before name configuration bytes = .ret after returned

/-- Flapjack infrastructure: HOL's empty external call supplies a genuine
successful step for every native FFI state, independently of its oracle. -/
theorem callFFIRelHOL_refl {σ : Type} (state : HolFfiState σ) :
    callFFIRelHOL state state := by
  refine ⟨.extCall (Basis.Pure.MlString.MlString.implode []), [], [], [], ?_⟩
  simp [callFFIHOL]

end Flapjack
