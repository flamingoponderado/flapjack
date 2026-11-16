module

public import Flapjack.TypeSoundInvariants
public import Flapjack.TypeSystemHOL.Declarations
public import Flapjack.NamespaceProps

@[expose] public section

/-! Well-formed declarative environments are closed under extension. -/
namespace Flapjack.TypeSysProps
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.TypeSoundInvariants

@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "extend_dec_tenv_ok"]
theorem extendDecTenvOk (tenv tenv' : TypeEnv)
    (h : tenvOk tenv ∧ tenvOk tenv') : tenvOk (extendDecTenv tenv tenv') := by
  refine ⟨?_, ?_, ?_⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.1, h.2.1⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.2.1, h.2.2.1⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.2.2, h.2.2.2⟩

end Flapjack.TypeSysProps
