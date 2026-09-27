import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite

/-!
# PanSem ShMemLoad equation (tag withheld)

This case is kept in its own module so case work can proceed independently of
the shared `EvaluateFinite` clause file. Its conclusion spells out the two
source matches from `panSemScript.sml:605-610`: first `eval s ad`, then
`lookup_kvar vk v s`; each failed check returns `(SOME Error, s)`.

The state carrier is `PanSemStateFiniteExact`; its four finite maps are the
reviewed canonical `HolFiniteMapExact` translation. The `@[hol]` tag is
withheld because the successful branch calls `shMemLoadHOLExact` on
`state.toExact`. That helper is typed over `PanSemStateExact`, whose four map
fields are unrestricted lookup functions. Repacking its result with `ofExact`
proves support preservation for this input but does not change the helper's
declared carrier. A faithful finite-carrier `sh_mem_load_def` and a case
statement using it directly are tracked by `flapjack-qj5.10.1`. This theorem
does not add a decidability premise: the shared-memory predicate is decided
classically, as the pair evaluator does.
-/

namespace Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase

open Flapjack.Pancake.PanLang (ExpHOL MlS ProgHOL)

theorem ofExact_toExact_any {width : Nat} {σ : Type} [NeZero width]
    (state : Flapjack.PanSemStateFiniteExact width σ)
    (support : state.toExact.FiniteSupport) :
    Flapjack.PanSemStateFiniteExact.ofExact state.toExact support = state := by
  cases state
  rfl

/-- Flapjack-specific ShMemLoad case equation. The exact HOL tag remains
    withheld for the helper-carrier mismatch documented at module scope. -/
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
              let loaded := @Flapjack.shMemLoadHOLExact width σ _ state.toExact
                (fun current => Classical.propDecidable (state.shMemaddrs current))
                kind name addr (Flapjack.nbOpHOL operator)
              (loaded.1, Flapjack.PanSemStateFiniteExact.ofExact loaded.2
                (@Flapjack.shMemLoadHOLExact_finiteSupport width σ _ state.toExact
                  (fun current => Classical.propDecidable (state.shMemaddrs current))
                  kind name addr (Flapjack.nbOpHOL operator)
                  state.toExact_finiteSupport))
          | _ => (some .error, state)
      | _ => (some .error, state) := by
  classical
  simp [Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteState,
    Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteStateWithDeciders,
    Flapjack.PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext,
    Flapjack.shMemLoadClauseHOLExact,
    Flapjack.PanSemStateFiniteExact.evalHOLFinite_eq_toExact] <;>
    repeat' split <;> simp_all <;> try apply ofExact_toExact_any

end Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase
