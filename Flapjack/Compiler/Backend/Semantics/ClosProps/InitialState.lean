module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.HolRef

@[expose] public section

/-! Initial closure-state projection lemmas from the original `closProps`
script. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Closure states use the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The initial state keeps the supplied arity bound. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "initial_state_max_app"
  (fmap_as_finite_support := [refs, code])]
theorem initialState_maxApp {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (clock : Nat) :
    (initialState ffi maxApp code oracle compiler clock : State C F).maxApp = maxApp := by
  simp [initialState]

/-- The initial state stores the supplied clock, and rewriting that clock to a
new value is the same as starting with that value. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "initial_state_clock"
  (fmap_as_finite_support := [refs, code])]
theorem initialState_clock {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (clock : Nat) (otherClock : Nat) :
    (initialState ffi maxApp code oracle compiler clock : State C F).clock = clock ∧
      { initialState ffi maxApp code oracle compiler otherClock with clock := clock } =
        initialState ffi maxApp code oracle compiler clock := by
  constructor
  · simp [initialState]
  · simp [initialState]

/-- Adding clock to the initial state is the same as starting with the sum. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "initial_state_with_clock"
  (fmap_as_finite_support := [refs, code])]
theorem initialState_withClock {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (clock : Nat) (extra : Nat) :
    { initialState ffi maxApp code oracle compiler clock with
        clock := (initialState ffi maxApp code oracle compiler clock : State C F).clock + extra } =
      initialState ffi maxApp code oracle compiler (clock + extra) := by
  simp [initialState]

end Flapjack.Compiler.Backend.ClosProps
