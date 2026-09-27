import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite

/-!
# ExtCall finite-carrier case import shim

The tagged `evaluate_def` ExtCall equation is declared in
`StateExactFiniteMap.lean`, beside `PanSemStateFiniteExact`, the carrier that
owns the four maps and canonical finite-support witness. This module keeps the
older namespace-level name as an untagged alias for parity callers; it is not a
second HOL declaration.
-/

namespace Flapjack.Pancake.Semantics.PanSem.ExtCallCase

open Flapjack.Pancake.PanLang (ExpHOL MlS ProgHOL)

/-- Flapjack-specific alias for the owner-module theorem; it has no separate
    HOL original. -/
abbrev evaluateHOLFiniteState_extCall_source {width : Nat} {σ : Type}
    [NeZero width] (state : Flapjack.PanSemStateFiniteExact width σ)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL width) :=
  @Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteState_extCall_source width σ _
    state function configuration configurationLength array arrayLength

end Flapjack.Pancake.Semantics.PanSem.ExtCallCase
