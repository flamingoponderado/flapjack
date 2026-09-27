import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite

/-!
# ShMemLoad finite-carrier case import shim

The tagged `evaluate_def` ShMemLoad equation is declared in
`StateExactFiniteMap.lean`, beside `PanSemStateFiniteExact`, the carrier that
owns its four finite maps and canonical finite-support witness. This module
keeps the older namespace-level name as an untagged forwarder for the direct
ShMemLoad parity checks; it is not a second HOL declaration.
-/

namespace Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase

open Flapjack.Pancake.PanLang (ExpHOL MlS ProgHOL)

/- The tagged source theorem and its canonical finite-map witness live in
   `StateExactFiniteMap.lean`, alongside the carrier that owns the four map
   fields. This untagged namespace forwarder preserves the older case-module
   API for its parity checks; it is Flapjack-specific plumbing, not a second
   HOL declaration. -/
theorem evaluateHOLFiniteState_shMemLoad_source {width : Nat} {σ : Type}
    [NeZero width] (state : Flapjack.PanSemStateFiniteExact width σ)
    (operator : Flapjack.OpSize) (kind : Flapjack.VarKind) (name : MlS)
    (address : ExpHOL width) :
    Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.shMemLoad operator kind name address : ProgHOL width) =
      match @Flapjack.PanSemStateFiniteExact.evalHOLFinite width σ _ state
          (fun current => Classical.propDecidable (state.memaddrs current)) address with
      | some (.val (.word addr)) =>
          match Flapjack.PanSemStateFiniteExact.lookupKvarHOLFinite kind name state with
          | some (.val (.word _)) =>
              let loaded := @Flapjack.PanSemStateFiniteExact.shMemLoadHOLFiniteExact
                width σ _ state
                (fun current => Classical.propDecidable (state.shMemaddrs current))
                kind name addr (Flapjack.nbOpHOL operator)
              (loaded.1, loaded.2)
          | _ => (some .error, state)
      | _ => (some .error, state) :=
  Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source
    state operator kind name address

end Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase
