module

public import Flapjack.Compiler.Backend.ClosKnown.Fuel

@[expose] public section

/-! Source equations for the known-function pass's tick insertion. -/
namespace Flapjack.Compiler.Backend.ClosKnownProps

/-- Tick insertion unfolds at zero and at a successor count. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownPropsScript.sml" "mk_Ticks_alt"]
theorem mkTicksAlt :
    (∀ (t : BackendCommon.Tra) (tc : Nat) (e : ClosLang.Exp),
      ClosKnown.ticks t tc 0 e = e) ∧
    (∀ (t : BackendCommon.Tra) (tc n : Nat) (e : ClosLang.Exp),
      ClosKnown.ticks t tc (n + 1) e =
        ClosKnown.ticks t (tc + 1) n (.tick (BackendCommon.mkCons t tc) e)) := by
  constructor <;> intros <;> rfl

end Flapjack.Compiler.Backend.ClosKnownProps
